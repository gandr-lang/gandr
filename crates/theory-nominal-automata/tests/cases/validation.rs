//! Consumer-visible boundaries beyond the named floor.
use alloc::collections::BTreeSet;
use alloc::vec;

use gandr_theory_nominal_automata::handle::Arity;
use gandr_theory_nominal_automata::handle::AutomatonError;
use gandr_theory_nominal_automata::handle::Configuration;
use gandr_theory_nominal_automata::handle::Control;
use gandr_theory_nominal_automata::handle::Membership;
use gandr_theory_nominal_automata::handle::Register;
use gandr_theory_nominal_automata::handle::Store;
use gandr_theory_nominal_automata::handle::Transfer;
use gandr_theory_nominal_automata::letter::Letter;
use gandr_theory_nominal_automata::nda::Nda;
use gandr_theory_nominal_automata::nda::Rule;
use gandr_theory_nominal_automata::rnna::Rnna;
use gandr_theory_nominal_automata::rnna::RnnaRule;
use gandr_theory_nominal_automata::rnta::ChildTarget;
use gandr_theory_nominal_automata::rnta::NodeKind;
use gandr_theory_nominal_automata::rnta::Rnta;
use gandr_theory_nominal_automata::rnta::RntaRule;
use gandr_theory_nominal_automata::rnta::Term;
use gandr_theory_nominal_automata::rnta::TermError;
use gandr_theory_nominal_automata::rnta::TermId;
use gandr_theory_nominal_automata::rnta::TermNode;

use super::Name;
use super::Symbol;

#[test]
fn transfers_preserve_partial_injections()
{
    let q0 = Control::ZERO;
    for (transfer, error) in [
        (
            vec![Transfer::Keep(Register::from(2)), Transfer::Empty],
            AutomatonError::UnknownRegister {
                control: q0,
                register: Register::from(2),
            },
        ),
        (
            vec![
                Transfer::Keep(Register::ZERO),
                Transfer::Keep(Register::ZERO),
            ],
            AutomatonError::RepeatedRegister {
                control: q0,
                register: Register::ZERO,
            },
        ),
        (
            vec![Transfer::Allocated, Transfer::Allocated],
            AutomatonError::MisplacedAllocatedName { control: q0 },
        ),
    ] {
        let initial = Configuration::new(q0, Store::<Name>::empty(Arity::from(2)));
        assert_eq!(
            Nda::new(
                vec![Arity::from(2)],
                initial.clone(),
                BTreeSet::new(),
                vec![Rule::open(q0, q0, transfer.clone())]
            ),
            Err(error)
        );
        assert_eq!(
            Rnna::new(
                vec![Arity::from(2)],
                initial.clone(),
                BTreeSet::new(),
                vec![RnnaRule::allocate(q0, q0, transfer.clone())]
            ),
            Err(error)
        );
        assert_eq!(
            Rnta::new(vec![Arity::from(2)], initial, vec![RntaRule::new(
                q0,
                Symbol::Node,
                NodeKind::Allocate,
                vec![ChildTarget::new(q0, transfer)]
            )]),
            Err(error)
        );
    }
}
#[test]
fn epsilon_cycles_and_nondeterminism_preserve_membership()
{
    let q0 = Control::ZERO;
    let q1 = Control::from(1);
    let q2 = Control::from(2);
    let q3 = Control::from(3);
    let automaton = Nda::new(
        vec![Arity::from(1); 4],
        Configuration::new(q0, Store::<Name>::empty(Arity::from(1))),
        BTreeSet::from([q3]),
        vec![
            Rule::forget(q0, Register::ZERO, q0, vec![Transfer::Empty]),
            Rule::open(q0, q1, vec![Transfer::Allocated]),
            Rule::open(q0, q2, vec![Transfer::Allocated]),
            Rule::free(q2, Register::ZERO, q2, vec![Transfer::Keep(Register::ZERO)]),
            Rule::forget(q2, Register::ZERO, q3, vec![Transfer::Empty]),
        ],
    )
    .expect("finite epsilon closure");
    assert_eq!(automaton.accepts(&[]), Membership::Rejected);
    assert_eq!(
        automaton.accepts(&[Letter::Open(Name::User)]),
        Membership::Accepted
    );
    assert_eq!(
        automaton.accepts(&[Letter::Open(Name::User), Letter::Free(Name::User)]),
        Membership::Accepted
    );
    assert_eq!(
        automaton.accepts(&[Letter::Open(Name::User), Letter::Free(Name::Other)]),
        Membership::Rejected
    );
}
#[test]
fn flat_terms_refuse_forward_children_and_handle_deep_scope()
{
    let mut arena = Term::default();
    let absent = TermId::from(0);
    assert_eq!(
        arena.push(TermNode::free(Name::User, Symbol::Node, vec![absent])),
        Err(TermError { node: absent })
    );
    assert_eq!(arena.free_names(absent), Err(TermError { node: absent }));
    let leaf = arena
        .push(TermNode::free(Name::User, Symbol::Leaf, vec![]))
        .expect("leaf");
    assert_eq!(leaf, absent);
    assert_eq!(
        arena.node(leaf).expect("valid node").symbol(),
        &Symbol::Leaf
    );
    let mut root = leaf;
    for _ in 0_usize .. 10_000 {
        root = arena
            .push(TermNode::bound(Name::Admin, Symbol::Node, vec![root]))
            .expect("backward reference");
    }
    assert_eq!(arena.free_names(root), Ok(BTreeSet::from([Name::User])));
    let closed = arena
        .push(TermNode::bound(Name::User, Symbol::Node, vec![root]))
        .expect("backward reference");
    assert_eq!(arena.free_names(closed), Ok(BTreeSet::new()));
    drop(arena);
}
