//! Tree-handle and free-name floor.
use alloc::collections::BTreeSet;
use alloc::vec;

use gandr_theory_nominal_automata::handle::Arity;
use gandr_theory_nominal_automata::handle::AutomatonError;
use gandr_theory_nominal_automata::handle::Configuration;
use gandr_theory_nominal_automata::handle::Control;
use gandr_theory_nominal_automata::handle::Register;
use gandr_theory_nominal_automata::handle::Store;
use gandr_theory_nominal_automata::handle::Transfer;
use gandr_theory_nominal_automata::rnta::ChildTarget;
use gandr_theory_nominal_automata::rnta::NodeKind;
use gandr_theory_nominal_automata::rnta::Rnta;
use gandr_theory_nominal_automata::rnta::RntaRule;
use gandr_theory_nominal_automata::rnta::Term;
use gandr_theory_nominal_automata::rnta::TermNode;

use super::Name;
use super::Symbol;

#[test]
fn free_names_respects_binder_shadowing()
{
    let mut term = Term::default();
    let bound_leaf = term
        .push(TermNode::free(Name::Admin, Symbol::Leaf, vec![]))
        .expect("leaf");
    let free_leaf = term
        .push(TermNode::free(Name::User, Symbol::Leaf, vec![]))
        .expect("leaf");
    let binder = term
        .push(TermNode::bound(Name::Admin, Symbol::Node, vec![
            bound_leaf, free_leaf,
        ]))
        .expect("backward children");
    assert_eq!(term.free_names(binder), Ok(BTreeSet::from([Name::User])));
    let outer = term
        .push(TermNode::free(Name::Admin, Symbol::Node, vec![binder]))
        .expect("backward child");
    assert_eq!(
        term.free_names(outer),
        Ok(BTreeSet::from([Name::Admin, Name::User]))
    );
    let nested = term
        .push(TermNode::bound(Name::Admin, Symbol::Node, vec![
            binder, bound_leaf,
        ]))
        .expect("backward children");
    assert_eq!(term.free_names(nested), Ok(BTreeSet::from([Name::User])));
    let sibling = term
        .push(TermNode::bound(Name::Other, Symbol::Node, vec![
            nested, bound_leaf,
        ]))
        .expect("backward children");
    assert_eq!(
        term.free_names(sibling),
        Ok(BTreeSet::from([Name::Admin, Name::User]))
    );
}
#[test]
fn construction_accepts_a_well_formed_rnta()
{
    let q0 = Control::ZERO;
    let q1 = Control::from(1);
    let automaton = Rnta::new(
        vec![Arity::ZERO, Arity::from(1)],
        Configuration::new(q0, Store::<Name>::empty(Arity::ZERO)),
        vec![
            RntaRule::new(q0, Symbol::Node, NodeKind::Allocate, vec![
                ChildTarget::new(q1, vec![Transfer::Allocated]),
                ChildTarget::new(q1, vec![Transfer::Allocated]),
            ]),
            RntaRule::new(
                q1,
                Symbol::Leaf,
                NodeKind::FreeName {
                    register: Register::ZERO,
                },
                vec![],
            ),
        ],
    )
    .expect("each child may retain the allocated name");
    assert_eq!(usize::from(automaton.degree()), 1);
    assert_eq!(automaton.rules()[0].children()[0].transfer(), &[
        Transfer::Allocated
    ]);
    assert_eq!(automaton.rules()[0].children()[1].transfer(), &[
        Transfer::Allocated
    ]);
}
#[test]
fn construction_rejects_unknown_register()
{
    let q0 = Control::ZERO;
    assert_eq!(
        Rnta::new(
            vec![Arity::ZERO],
            Configuration::new(q0, Store::<Name>::empty(Arity::ZERO)),
            vec![RntaRule::new(
                q0,
                Symbol::Leaf,
                NodeKind::FreeName {
                    register: Register::ZERO
                },
                vec![]
            )]
        ),
        Err(AutomatonError::UnknownRegister {
            control: q0,
            register: Register::ZERO
        })
    );
}
#[test]
fn construction_rejects_misplaced_allocated_name()
{
    let q0 = Control::ZERO;
    assert_eq!(
        Rnta::new(
            vec![Arity::from(1)],
            Configuration::new(q0, Store::<Name>::empty(Arity::from(1))),
            vec![RntaRule::new(
                q0,
                Symbol::Node,
                NodeKind::FreeName {
                    register: Register::ZERO
                },
                vec![ChildTarget::new(q0, vec![Transfer::Allocated])]
            )]
        ),
        Err(AutomatonError::MisplacedAllocatedName { control: q0 })
    );
}
