//! Allocation-only word-handle floor.
use alloc::collections::BTreeSet;
use alloc::vec;

use gandr_theory_nominal_automata::handle::Arity;
use gandr_theory_nominal_automata::handle::AutomatonError;
use gandr_theory_nominal_automata::handle::Configuration;
use gandr_theory_nominal_automata::handle::Control;
use gandr_theory_nominal_automata::handle::Register;
use gandr_theory_nominal_automata::handle::Store;
use gandr_theory_nominal_automata::handle::Transfer;
use gandr_theory_nominal_automata::rnna::Rnna;
use gandr_theory_nominal_automata::rnna::RnnaRule;

use super::Name;

#[test]
fn construction_accepts_a_well_formed_rnna()
{
    let q0 = Control::ZERO;
    let q1 = Control::from(1);
    let automaton = Rnna::new(
        vec![Arity::ZERO, Arity::from(1)],
        Configuration::new(q0, Store::<Name>::empty(Arity::ZERO)),
        BTreeSet::from([q1]),
        vec![
            RnnaRule::allocate(q0, q1, vec![Transfer::Allocated]),
            RnnaRule::free(q1, Register::ZERO, q1, vec![Transfer::Keep(Register::ZERO)]),
        ],
    )
    .expect("valid handle");
    assert_eq!(usize::from(automaton.degree()), 1);
    assert_eq!(automaton.rules()[0].transfer(), &[Transfer::Allocated]);
    assert_eq!(automaton.rules()[1].transfer(), &[Transfer::Keep(
        Register::ZERO
    )]);
}
#[test]
fn construction_rejects_misplaced_allocated_name()
{
    let q0 = Control::ZERO;
    assert_eq!(
        Rnna::new(
            vec![Arity::from(1)],
            Configuration::new(q0, Store::<Name>::empty(Arity::from(1))),
            BTreeSet::new(),
            vec![RnnaRule::free(q0, Register::ZERO, q0, vec![
                Transfer::Allocated
            ])]
        ),
        Err(AutomatonError::MisplacedAllocatedName { control: q0 })
    );
}
