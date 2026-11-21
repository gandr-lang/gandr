use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;
use core::fmt::Write as _;

use gandr_kernel_term::FixpointEvidence;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;

use super::*;
use crate::boundary::ProducerArity;

/// The decimal digits a test literal is spelled with.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
struct Digits(&'static str);

/// The non-negative integer value spelled by `digits`.
///
/// # Specification
/// - requires: digits is a nonempty unsigned decimal spelling.
/// - ensures: that nonnegative integer as a literal heap value, with leading
///   zeroes removed except for zero itself.
/// - provides: numeric fixture values independent of their heap address.
/// - panics: on a malformed decimal spelling.
///
/// # Adequacy
/// - hypothesis: L3 — valid decimal fixtures used by heap identity and binding
///   scenarios have their canonical payload checked under enforcement. These
///   distinguish the wrong literal kind, sign or value; malformed spellings are
///   outside the fixture domain.
/// - witness: `store::tests::environments_bind_innermost_first`
/// - witness: `store::tests::heap_reads_preserve_identity_at_the_end`
#[spec(
        requires: !digits.0.is_empty() && digits.0.bytes().all(|byte| byte.is_ascii_digit()),
        ensures: |ref ret| match *ret {
            | HeapValue::Literal(Literal::Integer(ref integer)) => {
                let significant = digits.0.trim_start_matches('0');
                let expected = if significant.is_empty() { "0" } else { significant };
                let actual: &str = integer.magnitude().as_ref();
                integer.sign() == Sign::NonNegative && actual == expected
            },
            | _ => false,
        },
    )]
fn integer(digits: Digits) -> HeapValue
{
    HeapValue::Literal(Literal::Integer(IntegerLiteral::new(
        Sign::NonNegative,
        Magnitude::from_decimal_text(String::from(digits.0)).expect("decimal digits"),
    )))
}

/// Bindings are walked innermost first, and extending an environment leaves
/// the one it extended as it was.
#[test]
fn environments_bind_innermost_first()
{
    let mut store = Store::new();
    let first = store.allocate(integer(Digits("1"))).expect("room");
    let second = store.allocate(integer(Digits("2"))).expect("room");
    assert_eq!(None, store.bound_values(Environment::EMPTY).next());
    let outer = store.bind_value(Environment::EMPTY, first).expect("room");
    let inner = store.bind_value(outer, second).expect("room");
    assert_eq!(
        alloc::vec![second, first],
        store.bound_values(inner).collect::<Vec<_>>(),
        "the walk reads the chain innermost first"
    );
    assert_eq!(
        alloc::vec![first],
        store.bound_values(outer).collect::<Vec<_>>(),
        "the extended environment is unchanged"
    );
}

/// A chain whose innermost link names no binding of the store binds
/// nothing.
#[test]
fn a_dangling_chain_binds_nothing()
{
    let store = Store::new();
    let dangling = Environment {
        values: ValueScope::Innermost(ValueBindingId::from(u32::MAX)),
    };
    assert_eq!(None, store.bound_values(dangling).next());
}

/// The value family retains exact identities at its allocation boundaries.
#[test]
fn heap_reads_preserve_identity_at_the_end()
{
    let mut store = Store::new();
    assert_eq!(None, store.value(HeapValueId::from(0_u32)));
    let first = store.allocate(integer(Digits("11"))).expect("room");
    let last = store.allocate(integer(Digits("29"))).expect("room");
    assert_eq!(HeapValueId::from(0_u32), first);
    assert_eq!(HeapValueId::from(1_u32), last);
    assert_eq!(Some(&integer(Digits("11"))), store.value(first));
    assert_eq!(Some(&integer(Digits("29"))), store.value(last));
    assert_eq!(None, store.value(HeapValueId::from(2_u32)));
}

/// One step of a spelling: a value to spell, or the close of one spelled.
#[derive(Clone, Copy, Debug)]
enum Spelt
{
    /// Spell this value, then what it reaches.
    Value(HeapValueId),
    /// Close the value spelled last.
    Close,
}

/// The value `store` holds at `root`, each address spelled as what it holds:
/// two values spelled alike read alike in their stores, whatever their
/// addresses.
///
/// # Specification
/// trivial.
fn spelled(
    store: &Store,
    root: HeapValueId,
) -> String
{
    let mut spelled = String::new();
    let mut pending = Vec::from([Spelt::Value(root)]);
    while let Some(step) = pending.pop() {
        let Spelt::Value(id) = step
        else {
            spelled.push(')');
            continue;
        };
        let Some(value) = store.value(id)
        else {
            spelled.push_str("dangling");
            continue;
        };
        let (head, reached): (String, Vec<HeapValueId>) = match *value {
            HeapValue::Constructed {
                ref tag,
                ref fields,
            } => (format!("{tag:?}"), fields.to_vec()),
            HeapValue::Thunk { body, environment } => (
                format!("thunk {}", u32::from(body)),
                store.bound_values(environment).collect(),
            ),
            HeapValue::Fixpoint {
                body,
                environment,
                evidence,
            } => (
                format!("fixpoint {} {evidence:?}", u32::from(body)),
                store.bound_values(environment).collect(),
            ),
            HeapValue::Closure {
                producer,
                environment,
            } => (
                format!("closure {}", u32::from(producer)),
                store.bound_values(environment).collect(),
            ),
            HeapValue::Stack { ref frames } => {
                let mut head = String::from("stack");
                let mut reached = Vec::new();
                for frame in frames {
                    match *frame {
                        StackFrame::Apply(argument) => {
                            head.push_str(" apply");
                            reached.push(argument);
                        },
                        StackFrame::Bind(closed) => {
                            write!(head, " bind {}", u32::from(closed.body))
                                .expect("a string takes it");
                            reached.extend(store.bound_values(closed.environment));
                        },
                        StackFrame::Project(component) => {
                            write!(head, " project {}", usize::from(component))
                                .expect("a string takes it");
                        },
                    }
                }
                (head, reached)
            },
            HeapValue::Accumulated { of, by } => match by {
                Accumulation::Forced => (String::from("forced"), Vec::from([of])),
                Accumulation::Applied(argument) => {
                    (String::from("applied"), Vec::from([of, argument]))
                },
            },
            HeapValue::Literal(_)
            | HeapValue::Opaque(_)
            | HeapValue::Code(_)
            | HeapValue::Capability
            | HeapValue::Free { .. } => (format!("{value:?}"), Vec::new()),
        };
        spelled.push_str(&head);
        spelled.push('(');
        pending.push(Spelt::Close);
        pending.extend(reached.into_iter().rev().map(Spelt::Value));
    }
    spelled
}

/// A fixpoint whose chain binds a pair holding one integer twice, beside a
/// closure sharing that chain and a stack whose bind frame closes over it,
/// copies into a store that holds a value already. The copy reads as its
/// source, and it holds the integer once and the shared link once.
#[test]
fn a_copy_reads_as_its_source_and_keeps_its_sharing()
{
    let mut source = Store::new();
    let one = source.allocate(integer(Digits("1"))).expect("room");
    let pair = source
        .allocate(HeapValue::Constructed {
            tag: ConstructorTag::Tuple(ProducerArity::from(2_usize)),
            fields: Box::new([one, one]),
        })
        .expect("room");
    let chain = source.bind_value(Environment::EMPTY, pair).expect("room");
    let fixpoint = source
        .allocate(HeapValue::Fixpoint {
            body: CommandId::from(7_u32),
            environment: chain,
            evidence: FixpointEvidence::Partial,
        })
        .expect("room");
    let closure = source
        .allocate(HeapValue::Closure {
            producer: ProducerId::from(3_u32),
            environment: chain,
        })
        .expect("room");
    let stack = source
        .allocate(HeapValue::Stack {
            frames: Box::new([
                StackFrame::Apply(fixpoint),
                StackFrame::Bind(ClosedCommand {
                    body: CommandId::from(9_u32),
                    environment: chain,
                }),
            ]),
        })
        .expect("room");
    let root = source
        .allocate(HeapValue::Constructed {
            tag: ConstructorTag::Tuple(ProducerArity::from(3_usize)),
            fields: Box::new([fixpoint, closure, stack]),
        })
        .expect("room");

    let mut target = Store::new();
    let _held = target.allocate(integer(Digits("5"))).expect("room");
    let copied = target.copy(&source, root).expect("the value copies");

    assert_eq!(
        spelled(&source, root),
        spelled(&target, copied),
        "the copy reads as its source"
    );
    assert_eq!(
        7_usize,
        usize::from(target.values.len()),
        "the held value and six copied ones: the integer is copied once"
    );
    assert_eq!(
        1_usize,
        usize::from(target.value_bindings.len()),
        "the shared link is copied once"
    );
}

/// A capability does not copy, wherever it is held, and neither does a
/// dangling address nor a value closing over a dangling chain.
#[test]
fn a_capability_and_a_dangling_address_do_not_copy()
{
    let mut source = Store::new();
    let capability = source.allocate(HeapValue::Capability).expect("room");
    let held = source
        .allocate(HeapValue::Constructed {
            tag: ConstructorTag::Tuple(ProducerArity::from(1_usize)),
            fields: Box::new([capability]),
        })
        .expect("room");
    let unbound = source
        .allocate(HeapValue::Thunk {
            body: CommandId::from(2_u32),
            environment: Environment {
                values: ValueScope::Innermost(ValueBindingId::from(u32::MAX)),
            },
        })
        .expect("room");
    let mut target = Store::new();

    assert_eq!(
        Err(CopyRefusal::Capability(capability)),
        target.copy(&source, held),
        "a held capability is refused by name"
    );
    let nowhere = HeapValueId::from(9_u32);
    assert_eq!(
        Err(CopyRefusal::Dangling(nowhere)),
        target.copy(&source, nowhere),
        "a dangling address is refused by name"
    );
    assert_eq!(
        Err(CopyRefusal::Dangling(unbound)),
        target.copy(&source, unbound),
        "a value over a dangling chain is refused by name"
    );
}
