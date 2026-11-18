//! Tree-handle and free-name floor.
use alloc::collections::BTreeSet;
use alloc::string::ToString as _;
use alloc::vec;
use alloc::vec::Vec;

use gandr_theory_nominal_automata::handle::Arity;
use gandr_theory_nominal_automata::handle::AutomatonError;
use gandr_theory_nominal_automata::handle::Configuration;
use gandr_theory_nominal_automata::handle::Control;
use gandr_theory_nominal_automata::handle::Register;
use gandr_theory_nominal_automata::handle::Store;
use gandr_theory_nominal_automata::handle::Transfer;
use gandr_theory_nominal_automata::rnta::ChildTarget;
use gandr_theory_nominal_automata::rnta::NameKind;
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
/// A binder's scope ends with its subtree: a sibling after it that names
/// the same name names it free.
#[test]
fn a_name_is_free_again_past_its_binders_scope()
{
    let mut term = Term::default();
    let inside = term
        .push(TermNode::free(Name::User, Symbol::Leaf, vec![]))
        .expect("leaf");
    let binder = term
        .push(TermNode::bound(Name::User, Symbol::Node, vec![inside]))
        .expect("backward child");
    assert_eq!(term.free_names(binder), Ok(BTreeSet::new()));
    let outside = term
        .push(TermNode::free(Name::User, Symbol::Leaf, vec![]))
        .expect("leaf");
    let root = term
        .push(TermNode::free(Name::Other, Symbol::Node, vec![
            binder, outside,
        ]))
        .expect("backward children");
    assert_eq!(
        term.free_names(root),
        Ok(BTreeSet::from([Name::User, Name::Other]))
    );
}
/// A term keeps each node as pushed, and an unknown node is refused by
/// its index.
#[test]
fn a_term_reads_back_its_nodes_and_names_an_unknown_one()
{
    let mut term = Term::default();
    let leaf = term
        .push(TermNode::free(Name::User, Symbol::Leaf, vec![]))
        .expect("leaf");
    let binder = term
        .push(TermNode::bound(Name::Admin, Symbol::Node, vec![leaf, leaf]))
        .expect("backward children");
    let node = term.node(binder).expect("pushed");
    assert_eq!(node.name(), &NameKind::Bound(Name::Admin));
    assert_eq!(node.symbol(), &Symbol::Node);
    assert_eq!(node.children(), &[leaf, leaf]);
    assert_eq!(
        term.node(leaf).expect("pushed").name(),
        &NameKind::Free(Name::User)
    );
    let absent = TermId::from(7);
    assert_eq!(term.node(absent).err(), Some(TermError { node: absent }));
    let rendered = TermError { node: absent }.to_string();
    assert!(rendered.contains('7'), "{rendered}");
}
/// Validation keeps the presentation it accepts: the arities, the
/// initial configuration and every rule's source, symbol, constraint and
/// child controls, in the order given.
#[test]
fn a_validated_rnta_reads_back_its_presentation()
{
    let q0 = Control::ZERO;
    let q1 = Control::from(1);
    let initial = Configuration::new(q0, Store::<Name>::empty(Arity::ZERO));
    let read = NodeKind::FreeName {
        register: Register::ZERO,
    };
    let automaton = Rnta::new(vec![Arity::ZERO, Arity::from(1)], initial.clone(), vec![
        RntaRule::new(q0, Symbol::Node, NodeKind::Allocate, vec![
            ChildTarget::new(q1, vec![Transfer::Allocated]),
            ChildTarget::new(q0, vec![]),
        ]),
        RntaRule::new(q1, Symbol::Leaf, read, vec![]),
    ])
    .expect("valid handle");
    assert_eq!(automaton.arities(), &[Arity::ZERO, Arity::from(1)]);
    assert_eq!(automaton.initial(), &initial);
    let rules: Vec<_> = automaton
        .rules()
        .iter()
        .map(|rule| {
            let children: Vec<Control> = rule.children().iter().map(ChildTarget::control).collect();
            (rule.source(), *rule.symbol(), rule.kind(), children)
        })
        .collect();
    assert_eq!(rules, [
        (q0, Symbol::Node, NodeKind::Allocate, vec![q1, q0]),
        (q1, Symbol::Leaf, read, vec![]),
    ]);
}
