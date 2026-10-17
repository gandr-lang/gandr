use alloc::string::String;
use alloc::vec::Vec;

use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;

use super::*;

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
