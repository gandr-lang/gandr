//! Partial-store floor.
use alloc::string::String;
use alloc::string::ToString;
use alloc::vec;
use alloc::vec::Vec;

use gandr_theory_nominal_automata::handle::Arity;
use gandr_theory_nominal_automata::handle::AutomatonError;
use gandr_theory_nominal_automata::handle::Control;
use gandr_theory_nominal_automata::handle::Controls;
use gandr_theory_nominal_automata::handle::EmptyRegister;
use gandr_theory_nominal_automata::handle::Freshness;
use gandr_theory_nominal_automata::handle::Register;
use gandr_theory_nominal_automata::handle::RegisterAbsent;
use gandr_theory_nominal_automata::handle::Store;
use gandr_theory_nominal_automata::handle::StoreError;
use quenchant_shape::shape::Maybe::Absent;
use quenchant_shape::shape::Maybe::Present;

use super::Name;

#[test]
fn duplicate_assignment_is_rejected()
{
    assert_eq!(
        Store::try_new(vec![
            Present(Name::Admin),
            Absent(EmptyRegister::Empty),
            Present(Name::Admin)
        ]),
        Err(StoreError { atom: Name::Admin })
    );
}
#[test]
fn injective_partial_store_is_accepted()
{
    let store = Store::try_new(vec![
        Present(Name::Admin),
        Absent(EmptyRegister::Empty),
        Present(Name::User),
    ])
    .expect("injective");
    assert_eq!(store.arity(), Arity::from(3));
    assert_eq!(store.name(Register::ZERO), Present(Name::Admin));
    assert_eq!(store.name(Register::from(1)), Absent(RegisterAbsent::Empty));
    assert_eq!(store.name(Register::from(2)), Present(Name::User));
    assert_eq!(
        store.name(Register::from(3)),
        Absent(RegisterAbsent::OutOfRange)
    );
    assert_eq!(store.freshness(Name::Admin), Freshness::Remembered);
    assert_eq!(store.freshness(Name::Other), Freshness::Fresh);
}
#[test]
fn empty_store_has_only_empty_registers()
{
    let store = Store::<Name>::empty(Arity::from(2));
    assert_eq!(store.arity(), Arity::from(2));
    for index in 0 .. 2 {
        assert_eq!(
            store.name(Register::from(index)),
            Absent(RegisterAbsent::Empty)
        );
    }
    assert_eq!(
        store.name(Register::from(2)),
        Absent(RegisterAbsent::OutOfRange)
    );
    assert_eq!(store.freshness(Name::Admin), Freshness::Fresh);
}
/// Every structural error renders apart from the others and names the
/// controls, registers and arities it carries; a duplicate assignment
/// renders apart from them all without naming the caller's name.
#[test]
fn every_error_renders_apart_and_names_what_it_carries()
{
    let errors = [
        AutomatonError::InvalidControl {
            control: Control::from(3),
            controls: Controls::from(2),
        },
        AutomatonError::ArityMismatch {
            control: Control::from(4),
            expected: Arity::from(5),
            actual: Arity::from(6),
        },
        AutomatonError::UnknownRegister {
            control: Control::from(7),
            register: Register::from(8),
        },
        AutomatonError::RepeatedRegister {
            control: Control::from(9),
            register: Register::from(1),
        },
        AutomatonError::MisplacedAllocatedName {
            control: Control::from(2),
        },
        AutomatonError::KeptDeallocatedName {
            control: Control::from(3),
            register: Register::from(4),
        },
    ];
    let carried: [&[char]; 6] = [
        &['3', '2'],
        &['4', '5', '6'],
        &['7', '8'],
        &['9', '1'],
        &['2'],
        &['3', '4'],
    ];
    let mut rendered: Vec<String> = errors.iter().map(ToString::to_string).collect();
    for (text, digits) in rendered.iter().zip(carried) {
        for digit in digits {
            assert!(text.contains(*digit), "{text} omits {digit}");
        }
    }
    let duplicate = StoreError { atom: Name::Admin }.to_string();
    assert!(!duplicate.contains("Admin"), "{duplicate}");
    rendered.push(duplicate);
    let count = rendered.len();
    rendered.sort();
    rendered.dedup();
    assert_eq!(rendered.len(), count, "{rendered:?}");
}
