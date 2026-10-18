use alloc::string::String;

use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Side;
use gandr_kernel_term::Sign;

use super::*;

/// The decimal digits a test literal is spelled with.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Digits(&'static str);

/// The non-negative integer literal spelled by `digits`.
///
/// # Specification
/// trivial.
fn integer(digits: Digits) -> Literal
{
    Literal::Integer(IntegerLiteral::new(
        Sign::NonNegative,
        Magnitude::from_decimal_text(String::from(digits.0)).expect("decimal digits"),
    ))
}

/// Every head's producer arity, and each destructor's polarity, is pinned:
/// a change to the table is a change to what the check and the machine
/// accept.
#[test]
fn tag_arities_are_stable()
{
    let level = Level::zero();
    let cases = [
        (ConstructorTag::Tuple(ProducerArity::ZERO), 0_usize),
        (ConstructorTag::Tuple(ProducerArity::TWO), 2_usize),
        (ConstructorTag::Injection(Side::Left.into()), 1_usize),
        (ConstructorTag::Injection(Side::Right.into()), 1_usize),
        (ConstructorTag::Tuple(ProducerArity::from(3_usize)), 3_usize),
        (ConstructorTag::Injection(Summand::from(2_usize)), 1_usize),
        (ConstructorTag::Lift(level), 1_usize),
        (
            ConstructorTag::Data {
                tag: gandr_kernel_term::ConstructorTag::from(1_usize),
                arity: ProducerArity::from(3_usize),
                family: None,
            },
            3_usize,
        ),
        (ConstructorTag::Record(alloc::sync::Arc::from([])), 0_usize),
        (
            ConstructorTag::Record(alloc::sync::Arc::from([
                gandr_core_term::FieldLabel::from(String::from("a")),
                gandr_core_term::FieldLabel::from(String::from("s")),
            ])),
            2_usize,
        ),
    ];
    for (tag, arity) in cases {
        assert_eq!(
            ProducerArity::from(arity),
            tag.producer_arity(),
            "{tag:?} declares {arity} fields"
        );
    }
    assert_eq!(
        ProducerArity::ONE,
        DestructorTag::Apply.producer_arity(),
        "apply takes one argument"
    );
    assert_eq!(
        ProducerArity::ZERO,
        DestructorTag::Force.producer_arity(),
        "force takes none"
    );
    assert_eq!(
        Polarity::Negative,
        DestructorTag::Apply.polarity(),
        "a function is negative"
    );
    assert_eq!(
        Polarity::Positive,
        DestructorTag::Force.polarity(),
        "a thunk is positive"
    );
}

/// Every head declares its consumer arity: no constructor of the core's
/// positive types carries a consumer, and every destructor returns to
/// exactly one continuation.
#[test]
fn tag_consumer_arities_are_declared()
{
    for tag in [
        ConstructorTag::Tuple(ProducerArity::ZERO),
        ConstructorTag::Tuple(ProducerArity::TWO),
        ConstructorTag::Injection(Side::Left.into()),
        ConstructorTag::Injection(Side::Right.into()),
        ConstructorTag::Lift(Level::zero()),
        ConstructorTag::Data {
            tag: gandr_kernel_term::ConstructorTag::from(0_usize),
            arity: ProducerArity::TWO,
            family: None,
        },
        ConstructorTag::Record(alloc::sync::Arc::from([gandr_core_term::FieldLabel::from(
            String::from("a"),
        )])),
    ] {
        assert_eq!(
            ConsumerArity::ZERO,
            tag.consumer_arity(),
            "{tag:?} carries no consumer"
        );
    }
    for tag in [DestructorTag::Apply, DestructorTag::Force] {
        assert_eq!(
            ConsumerArity::ONE,
            tag.consumer_arity(),
            "{tag:?} returns to one continuation"
        );
    }
}

/// A minted node reads back as itself, and each family counts its own
/// nodes.
#[test]
fn arena_allocates_and_reads_back()
{
    let mut arena = CommandArena::new();
    let literal = ProducerNode::Literal(integer(Digits("7")));
    let producer = arena.mint_producer(literal.clone()).expect("a leaf mints");
    let consumer = arena
        .mint_consumer(ConsumerNode::Top)
        .expect("a leaf mints");
    let command = arena
        .mint_cut(Polarity::Positive, producer, consumer)
        .expect("both children resolve");
    assert_eq!(
        Some(&literal),
        arena.producer(producer),
        "the producer reads back"
    );
    assert_eq!(
        Some(&ConsumerNode::Top),
        arena.consumer(consumer),
        "the consumer reads back"
    );
    assert_eq!(
        Some(&CommandNode::Cut {
            polarity: Polarity::Positive,
            producer,
            consumer,
        }),
        arena.command(command),
        "the cut reads back"
    );
    assert_eq!(
        (
            NodeCount::from(1_usize),
            NodeCount::from(1_usize),
            NodeCount::from(1_usize)
        ),
        (
            arena.producer_count(),
            arena.consumer_count(),
            arena.command_count()
        ),
        "one node per family"
    );
}

/// A node over a child the arena does not hold is refused by the child's
/// family and address, and the arena is unchanged.
#[test]
fn minting_refuses_a_dangling_child()
{
    let mut arena = CommandArena::new();
    let top = arena
        .mint_consumer(ConsumerNode::Top)
        .expect("a leaf mints");
    let payload = arena
        .mint_producer(ProducerNode::Literal(integer(Digits("7"))))
        .expect("a leaf mints");
    let entry = arena.watermark();
    let phantom = ProducerId::from(3_u32);
    assert_eq!(
        Err(MintRefusal::DanglingProducer(phantom)),
        arena.mint_cut(Polarity::Positive, phantom, top),
        "the producer child dangles"
    );
    assert_eq!(
        Err(MintRefusal::DanglingCommand(CommandId::from(0_u32))),
        arena.mint_producer(ProducerNode::Mu {
            body: CommandId::from(0_u32),
        }),
        "the command child dangles"
    );
    assert_eq!(
        Err(MintRefusal::DanglingConsumer(ConsumerId::from(5_u32))),
        arena.mint_consumer(ConsumerNode::Destructor {
            tag: DestructorTag::Force,
            producers: Box::from([]),
            consumers: Box::from([ConsumerId::from(5_u32)]),
        }),
        "the consumer child dangles"
    );
    assert_eq!(
        Err(MintRefusal::DanglingCommand(CommandId::from(2_u32))),
        arena.mint_producer(ProducerNode::Fixpoint {
            body: CommandId::from(2_u32),
            evidence: gandr_kernel_term::FixpointEvidence::Partial,
        }),
        "the recursive thunk's body dangles"
    );
    assert_eq!(
        Err(MintRefusal::DanglingProducer(ProducerId::from(4_u32))),
        arena.mint_consumer(ConsumerNode::DataCase {
            branches: Box::from([ProducerId::from(4_u32)]),
            then: top,
        }),
        "a nominal match's branch dangles"
    );
    assert_eq!(
        Err(MintRefusal::DanglingConsumer(ConsumerId::from(6_u32))),
        arena.mint_consumer(ConsumerNode::DataCase {
            branches: Box::from([]),
            then: ConsumerId::from(6_u32),
        }),
        "a nominal match's continuation dangles"
    );
    assert_eq!(
        Err(MintRefusal::DanglingConsumer(ConsumerId::from(7_u32))),
        arena.mint_consumer(ConsumerNode::Select {
            selector: Selector::Component(gandr_core_term::Component::from(1_usize)),
            then: ConsumerId::from(7_u32),
        }),
        "a selection's continuation dangles"
    );
    let unannotated = gandr_core_term::CoreArena::new().value_type_unit();
    let signature =
        gandr_core_term::effect::EffectSig::new("E".into(), [gandr_core_term::effect::EffectOp {
            name: "op".into(),
            payload: unannotated,
            reply: unannotated,
        }])
        .expect("one operation");
    assert_eq!(
        Err(MintRefusal::DanglingAnnotation(unannotated)),
        arena.mint_command(CommandNode::Perform {
            signature,
            operation: "op".into(),
            route: Route::Nearest,
            payload,
            continuation: top,
        }),
        "a request's interface names a type the annotations do not hold"
    );
    assert_eq!(entry, arena.watermark(), "a refused mint appends nothing");
}

/// Truncation drops exactly the nodes minted after the mark: a dropped
/// address no longer resolves, and a kept one still does.
#[test]
fn truncation_drops_exactly_the_later_nodes()
{
    let mut arena = CommandArena::new();
    let kept = arena
        .mint_consumer(ConsumerNode::Top)
        .expect("a leaf mints");
    let mark = arena.watermark();
    let unit = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::ZERO),
            producers: Box::from([]),
            consumers: Box::from([]),
        })
        .expect("a leaf mints");
    let cut = arena
        .mint_cut(Polarity::Positive, unit, kept)
        .expect("children resolve");
    arena.truncate_to(mark);
    assert_eq!(mark, arena.watermark(), "the arena is back at its mark");
    assert_eq!(None, arena.producer(unit), "the later producer is dropped");
    assert_eq!(None, arena.command(cut), "the later command is dropped");
    assert_eq!(
        Some(&ConsumerNode::Top),
        arena.consumer(kept),
        "the earlier node is kept"
    );
}

/// Each family's offsets select its own exact nodes, including empty and
/// end boundaries.
#[test]
fn lookup_boundaries_follow_each_family()
{
    let mut arena = CommandArena::new();
    assert_eq!(None, arena.producer(ProducerId::from(0_u32)));
    assert_eq!(None, arena.consumer(ConsumerId::from(0_u32)));
    assert_eq!(None, arena.command(CommandId::from(0_u32)));
    let first = arena
        .mint_producer(ProducerNode::Constant(0_usize.into()))
        .expect("leaf");
    let last = arena
        .mint_producer(ProducerNode::Constant(7_usize.into()))
        .expect("leaf");
    let top = arena.mint_consumer(ConsumerNode::Top).expect("leaf");
    let covariable = ConsumerNode::Covariable(CovariableIndex::from(3_u32));
    let back = arena.mint_consumer(covariable.clone()).expect("leaf");
    let first_cut = CommandNode::Cut {
        polarity: Polarity::Positive,
        producer: first,
        consumer: top,
    };
    let last_cut = CommandNode::Cut {
        polarity: Polarity::Negative,
        producer: last,
        consumer: back,
    };
    let before = arena
        .mint_command(first_cut.clone())
        .expect("live children");
    let after = arena.mint_command(last_cut.clone()).expect("live children");
    assert_eq!(
        Some(&ProducerNode::Constant(0_usize.into())),
        arena.producer(first)
    );
    assert_eq!(
        Some(&ProducerNode::Constant(7_usize.into())),
        arena.producer(last)
    );
    assert_eq!(Some(&ConsumerNode::Top), arena.consumer(top));
    assert_eq!(Some(&covariable), arena.consumer(back));
    assert_eq!(Some(&first_cut), arena.command(before));
    assert_eq!(Some(&last_cut), arena.command(after));
    assert_eq!(None, arena.producer(ProducerId::from(2_u32)));
    assert_eq!(None, arena.consumer(ConsumerId::from(2_u32)));
    assert_eq!(None, arena.command(CommandId::from(2_u32)));
}

/// Future marks never grow truncated families, and the empty mark clears
/// all three.
#[test]
fn truncation_keeps_future_marks_and_drops_each_family()
{
    let mut arena = CommandArena::new();
    let empty = arena.watermark();
    let kept = arena
        .mint_producer(ProducerNode::Constant(0_usize.into()))
        .expect("leaf");
    let top = arena.mint_consumer(ConsumerNode::Top).expect("leaf");
    let cut = arena
        .mint_cut(Polarity::Positive, kept, top)
        .expect("live children");
    let mark = arena.watermark();
    let later = arena
        .mint_producer(ProducerNode::Constant(1_usize.into()))
        .expect("leaf");
    let back = arena
        .mint_consumer(ConsumerNode::Covariable(CovariableIndex::from(0_u32)))
        .expect("leaf");
    let dropped = arena
        .mint_cut(Polarity::Negative, later, back)
        .expect("live children");
    arena
        .mint_producer(ProducerNode::Constant(2_usize.into()))
        .expect("leaf");
    let future = arena.watermark();
    arena.truncate_to(mark);
    assert_eq!(mark, arena.watermark());
    assert_eq!(None, arena.producer(later));
    assert_eq!(None, arena.consumer(back));
    assert_eq!(None, arena.command(dropped));
    arena.truncate_to(future);
    assert_eq!(mark, arena.watermark());
    assert_eq!(
        Some(&ProducerNode::Constant(0_usize.into())),
        arena.producer(kept)
    );
    assert_eq!(Some(&ConsumerNode::Top), arena.consumer(top));
    assert_eq!(
        Some(&CommandNode::Cut {
            polarity: Polarity::Positive,
            producer: kept,
            consumer: top
        }),
        arena.command(cut)
    );
    arena.truncate_to(empty);
    assert_eq!(empty, arena.watermark());
    assert_eq!(None, arena.producer(kept));
    assert_eq!(None, arena.consumer(top));
    assert_eq!(None, arena.command(cut));
}

/// Every node form checks its distinct child positions before appending.
#[test]
fn every_node_form_checks_its_child_families()
{
    let mut arena = CommandArena::new();
    let leaf = arena
        .mint_producer(ProducerNode::Constant(0_usize.into()))
        .expect("leaf");
    let top = arena.mint_consumer(ConsumerNode::Top).expect("leaf");
    let body = arena
        .mint_cut(Polarity::Positive, leaf, top)
        .expect("live children");
    for node in [
        ProducerNode::Variable {
            zone: Zone::Intuitionistic,
            index: DeBruijnIndex::from(0_u32),
        },
        ProducerNode::Constant(1_usize.into()),
        ProducerNode::Literal(integer(Digits("17"))),
        ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::TWO),
            producers: Box::from([leaf]),
            consumers: Box::from([top]),
        },
        ProducerNode::Thunk { body },
        ProducerNode::Mu { body },
        ProducerNode::Cocase {
            arms: Box::from([CopatternArm {
                destructor: DestructorTag::Apply,
                body,
            }]),
        },
    ] {
        let id = arena
            .mint_producer(node.clone())
            .expect("all references live");
        assert_eq!(Some(&node), arena.producer(id));
    }
    for node in [
        ConsumerNode::Top,
        ConsumerNode::Covariable(CovariableIndex::from(4_u32)),
        ConsumerNode::MuTilde { body },
        ConsumerNode::Destructor {
            tag: DestructorTag::Apply,
            producers: Box::from([leaf]),
            consumers: Box::from([top]),
        },
        ConsumerNode::Case {
            arms: Box::from([PatternArm {
                constructor: ConstructorTag::Tuple(ProducerArity::ZERO),
                body,
            }]),
        },
        ConsumerNode::Select {
            selector: Selector::Label(gandr_core_term::FieldLabel::from(String::from("s"))),
            then: top,
        },
    ] {
        let id = arena
            .mint_consumer(node.clone())
            .expect("all references live");
        assert_eq!(Some(&node), arena.consumer(id));
    }
    let missing = CommandId::from(1_u32);
    let entry = arena.watermark();
    for node in [
        ProducerNode::Thunk { body: missing },
        ProducerNode::Mu { body: missing },
        ProducerNode::Cocase {
            arms: Box::from([
                CopatternArm {
                    destructor: DestructorTag::Apply,
                    body,
                },
                CopatternArm {
                    destructor: DestructorTag::Force,
                    body: missing,
                },
            ]),
        },
    ] {
        assert_eq!(
            Err(MintRefusal::DanglingCommand(missing)),
            arena.mint_producer(node)
        );
        assert_eq!(entry, arena.watermark());
    }
    for node in [
        ConsumerNode::MuTilde { body: missing },
        ConsumerNode::Case {
            arms: Box::from([
                PatternArm {
                    constructor: ConstructorTag::Tuple(ProducerArity::ZERO),
                    body,
                },
                PatternArm {
                    constructor: ConstructorTag::Tuple(ProducerArity::TWO),
                    body: missing,
                },
            ]),
        },
    ] {
        assert_eq!(
            Err(MintRefusal::DanglingCommand(missing)),
            arena.mint_consumer(node)
        );
        assert_eq!(entry, arena.watermark());
    }
}

/// Missing producer fields precede consumer fields, and each list keeps
/// field order.
#[test]
fn the_first_dangling_child_wins()
{
    let mut arena = CommandArena::new();
    let leaf = arena
        .mint_producer(ProducerNode::Constant(0_usize.into()))
        .expect("leaf");
    let top = arena.mint_consumer(ConsumerNode::Top).expect("leaf");
    let missing_producer = ProducerId::from(1_u32);
    let missing_consumer = ConsumerId::from(1_u32);
    let entry = arena.watermark();
    for (producers, consumers, expected) in [
        (
            &[leaf, missing_producer, ProducerId::from(2_u32)][..],
            &[missing_consumer][..],
            MintRefusal::DanglingProducer(missing_producer),
        ),
        (
            &[leaf][..],
            &[top, missing_consumer, ConsumerId::from(2_u32)][..],
            MintRefusal::DanglingConsumer(missing_consumer),
        ),
    ] {
        assert_eq!(
            Err(expected),
            arena.mint_producer(ProducerNode::Constructor {
                tag: ConstructorTag::Tuple(ProducerArity::TWO),
                producers: Box::from(producers),
                consumers: Box::from(consumers),
            })
        );
        assert_eq!(
            Err(expected),
            arena.mint_consumer(ConsumerNode::Destructor {
                tag: DestructorTag::Apply,
                producers: Box::from(producers),
                consumers: Box::from(consumers),
            })
        );
        assert_eq!(entry, arena.watermark());
    }
    assert_eq!(
        Err(MintRefusal::DanglingProducer(missing_producer)),
        arena.mint_cut(Polarity::Positive, missing_producer, missing_consumer)
    );
    assert_eq!(
        Err(MintRefusal::DanglingConsumer(missing_consumer)),
        arena.mint_cut(Polarity::Negative, leaf, missing_consumer)
    );
    assert_eq!(entry, arena.watermark());
}

/// The unit value, minted.
///
/// # Specification
/// trivial.
fn unit(arena: &mut CommandArena) -> ProducerId
{
    arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::ZERO),
            producers: Box::from([]),
            consumers: Box::from([]),
        })
        .expect("a leaf mints")
}

/// The intuitionistic variable `index`, minted.
///
/// # Specification
/// trivial.
fn variable(
    arena: &mut CommandArena,
    zone: Zone,
    index: DeBruijnIndex,
) -> ProducerId
{
    arena
        .mint_producer(ProducerNode::Variable { zone, index })
        .expect("a leaf mints")
}

/// The scope `node` carries.
///
/// # Specification
/// trivial.
fn scope_of(
    arena: &CommandArena,
    node: NodeAddress,
) -> NodeScope
{
    arena
        .node_scope(node)
        .cloned()
        .expect("a minted node carries a scope")
}

/// A binder's body selects its bound name exactly when it names it, and the
/// binder's own support never does: a `μ̃` over `x1` and over `x0`, a hold
/// over a body ignoring and a body naming its linear binder, and a `μ` over
/// `★` and over `α0`, one per zone.
#[test]
fn an_unused_binder_thins_to_zero()
{
    let mut arena = CommandArena::new();
    let terminal = arena.mint_consumer(ConsumerNode::Top).expect("leaf");
    let returned = arena
        .mint_consumer(ConsumerNode::Covariable(CovariableIndex::from(0_u32)))
        .expect("leaf");
    let zero = DeBruijnIndex::from(0_u32);

    for (named, selected) in [(1_u32, false), (0_u32, true)] {
        let occurrence = variable(&mut arena, Zone::Intuitionistic, DeBruijnIndex::from(named));
        let body = arena
            .mint_cut(Polarity::Positive, occurrence, terminal)
            .expect("children resolve");
        let binder = arena
            .mint_consumer(ConsumerNode::MuTilde { body })
            .expect("the body resolves");
        let inner = scope_of(&arena, NodeAddress::Command(body))
            .producers()
            .to_thinning();
        let outer = scope_of(&arena, NodeAddress::Consumer(binder))
            .producers()
            .to_thinning();
        assert_eq!(
            selected,
            inner
                .indices(Zone::Intuitionistic)
                .any(|index| index == zero),
            "μ̃ over x{named}"
        );
        assert_eq!(
            outer.indices(Zone::Intuitionistic).collect::<Vec<_>>(),
            named
                .checked_sub(1)
                .map(DeBruijnIndex::from)
                .into_iter()
                .collect::<Vec<_>>(),
            "μ̃ over x{named} lowers past its binder"
        );
    }

    let value = unit(&mut arena);
    let ignoring = arena
        .mint_cut(Polarity::Positive, value, returned)
        .expect("children resolve");
    let held = variable(&mut arena, Zone::Linear, DeBruijnIndex::from(0_u32));
    let naming = arena
        .mint_cut(Polarity::Positive, held, returned)
        .expect("children resolve");
    for (body, selected) in [(ignoring, false), (naming, true)] {
        let hold = arena
            .mint_command(CommandNode::Memory {
                form: gandr_core_term::memory::MemoryForm::Hold { value, body },
                continuation: terminal,
            })
            .expect("children resolve");
        let inner = scope_of(&arena, NodeAddress::Command(body))
            .producers()
            .to_thinning();
        assert_eq!(
            selected,
            inner.indices(Zone::Linear).any(|index| index == zero),
            "a hold whose body names its binder: {selected}"
        );
        assert_eq!(
            0,
            scope_of(&arena, NodeAddress::Command(hold))
                .producers()
                .indices(Zone::Linear)
                .len(),
            "the hold binds its own linear variable"
        );
    }

    for (consumer, selected) in [(terminal, false), (returned, true)] {
        let body = arena
            .mint_cut(Polarity::Positive, value, consumer)
            .expect("children resolve");
        let capture = arena
            .mint_producer(ProducerNode::Mu { body })
            .expect("the body resolves");
        let inner = scope_of(&arena, NodeAddress::Command(body))
            .covariables()
            .to_thinning();
        assert_eq!(
            selected,
            inner
                .indices(Zone::Intuitionistic)
                .any(|index| index == zero),
            "μ over a body naming α0: {selected}"
        );
        assert_eq!(
            0,
            scope_of(&arena, NodeAddress::Producer(capture))
                .covariables()
                .indices(Zone::Intuitionistic)
                .len(),
            "the μ binds its own covariable"
        );
    }
}

/// A suspension captures its support's intuitionistic indices past its own
/// former's binders, lowered past them: none for a thunk, the thunk itself
/// for a fixpoint, the argument for an `apply` arm, the value for a bind
/// frame; a body the arena does not hold captures nothing.
#[test]
fn captures_skip_each_suspensions_own_binders()
{
    let mut arena = CommandArena::new();
    let fields: Vec<ProducerId> = [0_u32, 1, 3]
        .into_iter()
        .map(|index| variable(&mut arena, Zone::Intuitionistic, DeBruijnIndex::from(index)))
        .collect();
    let triple = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::Tuple(ProducerArity::from(3_usize)),
            producers: fields.into_boxed_slice(),
            consumers: Box::from([]),
        })
        .expect("fields resolve");
    let returned = arena
        .mint_consumer(ConsumerNode::Covariable(CovariableIndex::from(0_u32)))
        .expect("leaf");
    let body = arena
        .mint_cut(Polarity::Positive, triple, returned)
        .expect("children resolve");
    let thunk = arena
        .mint_producer(ProducerNode::Thunk { body })
        .expect("the body resolves");
    let fixpoint = arena
        .mint_producer(ProducerNode::Fixpoint {
            body,
            evidence: gandr_kernel_term::FixpointEvidence::StructuralDescent,
        })
        .expect("the body resolves");
    let function = arena
        .mint_producer(ProducerNode::Cocase {
            arms: Box::from([CopatternArm {
                destructor: DestructorTag::Apply,
                body,
            }]),
        })
        .expect("the arm resolves");
    let stack = arena
        .mint_producer(ProducerNode::Reify(alloc::sync::Arc::from([
            gandr_core_term::control::StackFrame::Bind(body),
        ])))
        .expect("the frame resolves");
    let indices = |values: &[u32]| {
        values
            .iter()
            .map(|&index| DeBruijnIndex::from(index))
            .collect::<Vec<_>>()
    };
    for (suspension, expected) in [
        (Suspension::Thunk(body), indices(&[0, 1, 3])),
        (Suspension::Producer(thunk), indices(&[0, 1, 3])),
        (Suspension::Fixpoint(body), indices(&[0, 2])),
        (Suspension::Producer(fixpoint), indices(&[0, 2])),
        (Suspension::Producer(function), indices(&[0, 2])),
        (Suspension::Bind(body), indices(&[0, 2])),
    ] {
        let captures = arena.captures(suspension).expect("the suspension resolves");
        assert_eq!(expected.len(), captures.len(), "{suspension:?}");
        assert_eq!(
            expected,
            captures.clone().collect::<Vec<_>>(),
            "{suspension:?}"
        );
        assert!(
            expected.iter().rev().copied().eq(captures.rev()),
            "{suspension:?} reads from the outermost end"
        );
    }
    assert!(
        scope_of(&arena, NodeAddress::Producer(stack))
            .producers()
            .indices(Zone::Intuitionistic)
            .eq(indices(&[0, 2])),
        "a bind frame's stack has the frame body's support past its value"
    );
    assert!(
        arena
            .captures(Suspension::Thunk(CommandId::from(u32::MAX)))
            .is_none()
    );
    assert!(
        arena
            .captures(Suspension::Producer(ProducerId::from(u32::MAX)))
            .is_none()
    );
}

/// A fold's annotations count in its support: a fold whose element type
/// names `x3`, which no term of the fold names, has `x3` free, and the check
/// derives the same; a fold over closed types has none.
#[test]
fn an_annotation_counts_in_its_nodes_support()
{
    let mut arena = CommandArena::new();
    let code = arena
        .annotations_mut()
        .value_variable(Zone::Intuitionistic, DeBruijnIndex::from(3_u32));
    let open = arena
        .annotations_mut()
        .value_type_element(code, Level::zero());
    let closed = arena.annotations_mut().value_type_unit();
    let value = unit(&mut arena);
    let returned = arena
        .mint_consumer(ConsumerNode::Covariable(CovariableIndex::from(0_u32)))
        .expect("leaf");
    let branch = arena
        .mint_cut(Polarity::Positive, value, returned)
        .expect("children resolve");
    let terminal = arena.mint_consumer(ConsumerNode::Top).expect("leaf");
    let list = arena
        .mint_producer(ProducerNode::Constructor {
            tag: ConstructorTag::ListNil,
            producers: Box::from([]),
            consumers: Box::from([]),
        })
        .expect("a leaf mints");
    for (element, expected) in [
        (
            open,
            alloc::collections::BTreeSet::from([(
                Zone::Intuitionistic,
                DeBruijnIndex::from(3_u32),
            )]),
        ),
        (closed, alloc::collections::BTreeSet::new()),
    ] {
        let fold = arena
            .mint_consumer(ConsumerNode::ListFold {
                element,
                result: closed,
                on_nil: branch,
                on_cons: branch,
                continuation: terminal,
            })
            .expect("children resolve");
        let root = arena
            .mint_cut(Polarity::Positive, list, fold)
            .expect("children resolve");
        let free = crate::check::check_command(&arena, root).expect("the carried covers check");
        assert_eq!(&expected, free.producers());
    }
}
