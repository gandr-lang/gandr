//! Allocation-only word-handle floor.
use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;

use gandr_theory_nominal_automata::handle::Arity;
use gandr_theory_nominal_automata::handle::AutomatonError;
use gandr_theory_nominal_automata::handle::Configuration;
use gandr_theory_nominal_automata::handle::Control;
use gandr_theory_nominal_automata::handle::Register;
use gandr_theory_nominal_automata::handle::Store;
use gandr_theory_nominal_automata::handle::Transfer;
use gandr_theory_nominal_automata::rnna::Rnna;
use gandr_theory_nominal_automata::rnna::RnnaRule;
use gandr_theory_nominal_automata::rnna::RnnaRuleKind;

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
/// A free use of a register past its source control's arity is refused
/// by that control and register.
#[test]
fn construction_rejects_a_free_use_past_the_arity()
{
    let q0 = Control::ZERO;
    assert_eq!(
        Rnna::new(
            vec![Arity::from(1)],
            Configuration::new(q0, Store::<Name>::empty(Arity::from(1))),
            BTreeSet::new(),
            vec![RnnaRule::free(q0, Register::from(1), q0, vec![
                Transfer::Keep(Register::ZERO)
            ])]
        ),
        Err(AutomatonError::UnknownRegister {
            control: q0,
            register: Register::from(1),
        })
    );
}
/// Validation keeps the presentation it accepts: the arities, the
/// initial configuration, the accepting controls and every rule's source,
/// event and target, in the order given.
#[test]
fn a_validated_rnna_reads_back_its_presentation()
{
    let q0 = Control::ZERO;
    let q1 = Control::from(1);
    let initial = Configuration::new(q0, Store::<Name>::empty(Arity::ZERO));
    let automaton = Rnna::new(
        vec![Arity::ZERO, Arity::from(1)],
        initial.clone(),
        BTreeSet::from([q1]),
        vec![
            RnnaRule::allocate(q0, q1, vec![Transfer::Allocated]),
            RnnaRule::free(q1, Register::ZERO, q1, vec![Transfer::Keep(Register::ZERO)]),
        ],
    )
    .expect("valid handle");
    assert_eq!(automaton.arities(), &[Arity::ZERO, Arity::from(1)]);
    assert_eq!(automaton.initial(), &initial);
    assert_eq!(automaton.finals(), &BTreeSet::from([q1]));
    let rules: Vec<_> = automaton
        .rules()
        .iter()
        .map(|rule| (rule.source(), rule.kind(), rule.target()))
        .collect();
    assert_eq!(rules, [
        (q0, RnnaRuleKind::Allocate, q1),
        (
            q1,
            RnnaRuleKind::Free {
                register: Register::ZERO
            },
            q1
        ),
    ]);
}
