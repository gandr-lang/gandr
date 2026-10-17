use alloc::boxed::Box;

use gandr_core_term::Value;
use gandr_kernel_strata::Level;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Side;
use gandr_kernel_term::StringLiteral;
use gandr_theory_cell_complexes::Polarity;

use super::*;
use crate::boundary::ProducerArity;
use crate::il::ConsumerNode;
use crate::il::CopatternArm;
use crate::il::DestructorTag;

/// A shared graph retains distinct ordered payloads and every first-order
/// head.
#[test]
fn shared_fields_preserve_their_order()
{
    let arena = CommandArena::new();
    let mut store = Store::new();
    let literal = Literal::Text(StringLiteral::new("payload".into()));
    let unit = store
        .allocate(HeapValue::Constructed {
            tag: ConstructorTag::Tuple(ProducerArity::ZERO),
            fields: Box::from([]),
        })
        .expect("room");
    let opaque = store
        .allocate(HeapValue::Opaque(7_usize.into()))
        .expect("room");
    let text = store
        .allocate(HeapValue::Literal(literal.clone()))
        .expect("room");
    let pair = store
        .allocate(HeapValue::Constructed {
            tag: ConstructorTag::Tuple(ProducerArity::TWO),
            fields: Box::from([text, opaque]),
        })
        .expect("room");
    let injection = store
        .allocate(HeapValue::Constructed {
            tag: ConstructorTag::Injection(Side::Right.into()),
            fields: Box::from([unit]),
        })
        .expect("room");
    let lift = store
        .allocate(HeapValue::Constructed {
            tag: ConstructorTag::Lift(Level::zero()),
            fields: Box::from([injection]),
        })
        .expect("room");
    let branch = store
        .allocate(HeapValue::Constructed {
            tag: ConstructorTag::Tuple(ProducerArity::TWO),
            fields: Box::from([pair, lift]),
        })
        .expect("room");
    let root = store
        .allocate(HeapValue::Constructed {
            tag: ConstructorTag::Tuple(ProducerArity::TWO),
            fields: Box::from([branch, branch]),
        })
        .expect("room");
    let mut core = CoreArena::new();
    let mut reading = Reading::new(&arena, &store, &mut core);
    reading.read([root]).expect("closed first-order graph");
    let read_unit = reading.lookup(unit).expect("recorded");
    let read_opaque = reading.lookup(opaque).expect("recorded");
    let read_text = reading.lookup(text).expect("recorded");
    let read_pair = reading.lookup(pair).expect("recorded");
    let read_injection = reading.lookup(injection).expect("recorded");
    let read_lift = reading.lookup(lift).expect("recorded");
    let read_branch = reading.lookup(branch).expect("recorded");
    let read_root = reading.lookup(root).expect("recorded");
    for (id, expected) in [
        (read_unit, Value::unit()),
        (read_opaque, Value::Constant(7_usize.into())),
        (read_text, Value::Literal(literal)),
        (read_pair, Value::Tuple([read_text, read_opaque].into())),
        (
            read_injection,
            Value::Injection(Side::Right.into(), read_unit),
        ),
        (read_lift, Value::Lift {
            target: Level::zero(),
            body: read_injection,
        }),
        (read_branch, Value::Tuple([read_pair, read_lift].into())),
        (read_root, Value::Tuple([read_branch, read_branch].into())),
    ] {
        assert_eq!(Some(&expected), reading.core.value(id));
    }
}

/// Lookup distinguishes held from recorded values, and closing reverses
/// binding order.
#[test]
fn closing_records_innermost_values_and_exact_lookup()
{
    let arena = CommandArena::new();
    let mut store = Store::new();
    let outer = store
        .allocate(HeapValue::Constructed {
            tag: ConstructorTag::Tuple(ProducerArity::ZERO),
            fields: Box::from([]),
        })
        .expect("room");
    let inner = store
        .allocate(HeapValue::Opaque(7_usize.into()))
        .expect("room");
    let environment = store.bind_value(Environment::EMPTY, outer).expect("room");
    let environment = store.bind_value(environment, inner).expect("room");
    let mut core = CoreArena::new();
    let mut reading = Reading::new(&arena, &store, &mut core);
    assert_eq!(Err(ReadbackRefusal::Dangling(outer)), reading.lookup(outer));
    let closing = reading.closing(environment).expect("closed bindings");
    let inner_read = reading.lookup(inner).expect("recorded");
    let outer_read = reading.lookup(outer).expect("recorded");
    assert_eq!([inner_read, outer_read], closing.as_slice());
    assert_eq!(
        Some(&Value::Constant(7_usize.into())),
        reading.core.value(inner_read)
    );
    assert_eq!(Some(&Value::unit()), reading.core.value(outer_read));
    let missing = HeapValueId::from(u32::MAX);
    assert_eq!(
        Err(ReadbackRefusal::Dangling(missing)),
        reading.lookup(missing)
    );
}

/// Refusals after partial dependency or closing reads restore an existing
/// core prefix.
#[test]
fn refusals_restore_an_existing_core_prefix()
{
    let mut arena = CommandArena::new();
    let producer = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::ZERO),
            producers: Box::from([]),
            consumers: Box::from([]),
        })
        .expect("leaf");
    let top = arena.mint_consumer(ConsumerNode::Top).expect("leaf");
    let body = arena
        .mint_cut(Polarity::Positive, producer, top)
        .expect("references resolve");
    let capture = arena
        .mint_producer(ProducerNode::Mu { body })
        .expect("body resolves");
    let wrong_function = arena
        .mint_producer(ProducerNode::Cocase {
            arms: Box::from([CopatternArm {
                destructor: DestructorTag::Force,
                body,
            }]),
        })
        .expect("body resolves");
    let mut store = Store::new();
    let unit = store
        .allocate(HeapValue::Constructed {
            tag: ConstructorTag::Tuple(ProducerArity::ZERO),
            fields: Box::from([]),
        })
        .expect("room");
    let opaque = store
        .allocate(HeapValue::Opaque(7_usize.into()))
        .expect("room");
    let malformed = store
        .allocate(HeapValue::Constructed {
            tag: ConstructorTag::Tuple(ProducerArity::TWO),
            fields: Box::from([unit, opaque, unit]),
        })
        .expect("room");
    let environment = store.bind_value(Environment::EMPTY, opaque).expect("room");
    let captured = store
        .allocate(HeapValue::Closure {
            producer: capture,
            environment,
        })
        .expect("room");
    let function = store
        .allocate(HeapValue::Closure {
            producer: wrong_function,
            environment,
        })
        .expect("room");
    let cell = store.allocate_cell().expect("room");
    let thunk = store
        .allocate(HeapValue::Thunk {
            body,
            environment,
            cell,
        })
        .expect("room");
    let missing = HeapValueId::from(u32::MAX);
    let mut core = CoreArena::new();
    let prefix = core.value_constant(42_usize.into());
    let mark = core.watermark();
    for (value, positive_refusal, terminal_refusal) in [
        (
            missing,
            ReadbackRefusal::Dangling(missing),
            ReadbackRefusal::Dangling(missing),
        ),
        (
            malformed,
            ReadbackRefusal::Unreadable(malformed),
            ReadbackRefusal::Unreadable(malformed),
        ),
        (
            captured,
            ReadbackRefusal::Unreadable(captured),
            ReadbackRefusal::Unreadable(captured),
        ),
        (
            thunk,
            ReadbackRefusal::Decode(UnfocusRefusal::EscapingContinuation(top)),
            ReadbackRefusal::Decode(UnfocusRefusal::EscapingContinuation(top)),
        ),
        (
            function,
            ReadbackRefusal::Unreadable(function),
            ReadbackRefusal::Decode(UnfocusRefusal::ProducerOutsideTheImage(wrong_function)),
        ),
    ] {
        assert_eq!(
            Err(positive_refusal),
            read_back_value(&arena, &store, value, &mut core)
        );
        assert_eq!(mark, core.watermark());
        assert_eq!(
            Err(terminal_refusal),
            read_back_terminal(&arena, &store, value, &mut core)
        );
        assert_eq!(mark, core.watermark());
        assert_eq!(Some(&Value::Constant(42_usize.into())), core.value(prefix));
    }
}

/// A record reads back only from as many fields as its labels, under labels
/// in strictly ascending order.
#[test]
fn a_record_reads_back_only_from_one_field_per_ascending_label()
{
    use alloc::sync::Arc;

    use gandr_core_term::FieldLabel;

    let arena = CommandArena::new();
    let mut store = Store::new();
    let field = store
        .allocate(HeapValue::Opaque(7_usize.into()))
        .expect("room");
    let label = |text: &str| FieldLabel::from(alloc::string::String::from(text));
    let mut record = |labels: &[&str], fields: &[HeapValueId]| {
        store
            .allocate(HeapValue::Constructed {
                tag: ConstructorTag::Record(
                    labels.iter().map(|&text| label(text)).collect::<Arc<[_]>>(),
                ),
                fields: Box::from(fields),
            })
            .expect("room")
    };
    let read = record(&["a", "b"], &[field, field]);
    let refused = [
        record(&["a", "b"], &[field]),
        record(&["b", "a"], &[field, field]),
        record(&["a", "a"], &[field, field]),
    ];
    let mut core = CoreArena::new();
    let Ok(read) = read_back_value(&arena, &store, read, &mut core)
    else {
        panic!("an ascending record of two fields reads back");
    };
    let Some(&Value::Record(ref fields)) = core.value(read)
    else {
        panic!("a record");
    };
    assert!(fields.keys().eq([label("a"), label("b")].iter()));
    assert!(
        fields
            .values()
            .all(|&value| core.value(value) == Some(&Value::Constant(7_usize.into())))
    );
    for value in refused {
        assert_eq!(
            Err(ReadbackRefusal::Unreadable(value)),
            read_back_value(&arena, &store, value, &mut core)
        );
    }
}

/// A recorded run reads back only from one field per payload its moves
/// carry, each payload in its move.
#[test]
fn a_recorded_run_reads_back_only_from_one_field_per_payload()
{
    use alloc::sync::Arc;

    use gandr_core_term::session::RecordedMove;

    let arena = CommandArena::new();
    let mut store = Store::new();
    let field = store
        .allocate(HeapValue::Opaque(7_usize.into()))
        .expect("room");
    let mut run = |fields: &[HeapValueId]| {
        store
            .allocate(HeapValue::Constructed {
                tag: ConstructorTag::Recorded(Arc::from([
                    RecordedMove::Sent(()),
                    RecordedMove::Closed,
                ])),
                fields: Box::from(fields),
            })
            .expect("room")
    };
    let read = run(&[field]);
    let refused = [run(&[]), run(&[field, field])];
    let mut core = CoreArena::new();
    let Ok(read) = read_back_value(&arena, &store, read, &mut core)
    else {
        panic!("a send and a close read back from one payload");
    };
    let Some(&Value::Recorded(ref moves)) = core.value(read)
    else {
        panic!("a recorded run");
    };
    let [RecordedMove::Sent(payload), RecordedMove::Closed] = **moves
    else {
        panic!("a send, then a close: {moves:?}");
    };
    assert_eq!(core.value(payload), Some(&Value::Constant(7_usize.into())));
    for value in refused {
        assert_eq!(
            Err(ReadbackRefusal::Unreadable(value)),
            read_back_value(&arena, &store, value, &mut core)
        );
    }
}

/// A later-address dependency is rejected even when the store holds it.
#[test]
fn forward_dependencies_are_refused_before_reading_the_parent()
{
    let arena = CommandArena::new();
    let mut store = Store::new();
    let future = HeapValueId::from(1_u32);
    let parent = store
        .allocate(HeapValue::Constructed {
            tag: ConstructorTag::Tuple(ProducerArity::TWO),
            fields: Box::from([future, future]),
        })
        .expect("room");
    store
        .allocate(HeapValue::Opaque(7_usize.into()))
        .expect("room");
    let mut core = CoreArena::new();
    let mark = core.watermark();
    assert_eq!(
        Err(ReadbackRefusal::Dangling(future)),
        read_back_value(&arena, &store, parent, &mut core)
    );
    assert_eq!(mark, core.watermark());
    assert_eq!(
        Err(ReadbackRefusal::Dangling(future)),
        read_back_terminal(&arena, &store, parent, &mut core)
    );
    assert_eq!(mark, core.watermark());
}
