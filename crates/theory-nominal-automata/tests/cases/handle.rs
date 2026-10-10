//! Partial-store floor.
use alloc::vec;

use gandr_theory_nominal_automata::handle::Arity;
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
