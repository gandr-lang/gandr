//! The e-graph's classes, its rebuild and its redundant unions.

use alloc::vec;
use alloc::vec::Vec;

use gandr_theory_coherent_resolutions::Operation;
use gandr_theory_coherent_resolutions::TermPlace;
use gandr_theory_coherent_resolutions::TermTable;
use gandr_theory_coherent_resolutions::Variable;
use gandr_theory_e_graphs::Count;
use gandr_theory_e_graphs::Direction;
use gandr_theory_e_graphs::EGraph;
use gandr_theory_e_graphs::EGraphError;
use gandr_theory_e_graphs::EquationPlace;
use gandr_theory_e_graphs::Joined;
use gandr_theory_e_graphs::Reason;
use gandr_theory_e_graphs::Redundant;

use crate::fixtures::members;
use crate::fixtures::op;
use crate::fixtures::var;

/// The operations of the graph tests: four constants, then `f`.
const F: usize = 4;

#[test]
fn a_term_is_held_with_each_argument_once()
{
    let mut table = TermTable::default();
    let a = op(&mut table, Operation::from(0), &[]);
    let b = op(&mut table, Operation::from(1), &[]);
    let fa = op(&mut table, Operation::from(F), &[a]);
    let ffa = op(&mut table, Operation::from(F), &[fa]);
    let mut graph = EGraph::new(table, ());
    assert_eq!(graph.add(ffa), Ok(ffa));
    assert_eq!(graph.tally().nodes, Count::from(3_usize));
    assert_eq!(graph.add(ffa), Ok(ffa), "a held term keeps its class");
    assert_eq!(graph.add(fa), Ok(fa), "an argument is held with its parent");
    assert_eq!(graph.tally().nodes, Count::from(3_usize));
    assert_eq!(graph.find(a), Ok(a));
    assert_eq!(graph.find(b), Err(EGraphError::Unheld(b)));
}

#[test]
fn a_ground_equation_joins_its_sides_and_their_parents_after_the_rebuild()
{
    let mut table = TermTable::default();
    let a = op(&mut table, Operation::from(0), &[]);
    let b = op(&mut table, Operation::from(1), &[]);
    let fa = op(&mut table, Operation::from(F), &[a]);
    let fb = op(&mut table, Operation::from(F), &[b]);
    let mut graph = EGraph::new(table, ());
    for term in [fa, fb] {
        let _class = graph.add(term).expect("a table term");
    }
    let equation = graph.equation(a, b).expect("a ground equation");
    assert_eq!(graph.apply(equation, Vec::new()), Ok(Joined::Merged));
    assert_eq!(graph.find(a), graph.find(b));
    assert_ne!(
        graph.find(fa),
        graph.find(fb),
        "a union waits for the rebuild to join the parents"
    );
    graph.rebuild().expect("a rebuild");
    assert_eq!(graph.find(fa), graph.find(fb));
    assert_eq!(graph.tally().unions, Count::from(2_usize));
}

/// Four constants, `f` over each, and the three equations that chain the
/// constants: the parents of the constants' class join by congruence.
///
/// # Specification
/// trivial.
fn chain() -> (EGraph, Vec<EquationPlace>, Vec<TermPlace>)
{
    let mut table = TermTable::default();
    let constants: Vec<TermPlace> = (0 .. 4)
        .map(|place| op(&mut table, Operation::from(place), &[]))
        .collect();
    let parents: Vec<TermPlace> = constants
        .iter()
        .map(|&constant| op(&mut table, Operation::from(F), &[constant]))
        .collect();
    let mut graph = EGraph::new(table, ());
    for &parent in &parents {
        let _class = graph.add(parent).expect("a table term");
    }
    graph.rebuild().expect("a rebuild");
    let equations = constants
        .iter()
        .zip(constants.iter().skip(1))
        .map(|(&left, &right)| graph.equation(left, right).expect("a ground equation"))
        .collect();
    (graph, equations, parents)
}

#[test]
fn the_rebuild_repairs_each_class_once()
{
    // egg, § 3.2.1: a rebuild after the whole chain repairs the constants'
    // class once and the parents' class once; a rebuild after each union
    // repairs both classes for each of the three unions.
    let (mut deferred, equations, parents) = chain();
    let before = usize::from(deferred.tally().repairs);
    for &equation in &equations {
        let _joined = deferred.apply(equation, Vec::new()).expect("an instance");
    }
    deferred.rebuild().expect("a rebuild");
    let (mut eager, ..) = chain();
    let eager_before = usize::from(eager.tally().repairs);
    for &equation in &equations {
        let _joined = eager.apply(equation, Vec::new()).expect("an instance");
        eager.rebuild().expect("a rebuild");
    }
    assert_eq!(usize::from(deferred.tally().repairs) - before, 2);
    assert_eq!(usize::from(eager.tally().repairs) - eager_before, 6);
    for graph in [&deferred, &eager] {
        assert_eq!(members(graph, parents[0]), parents, "one class of parents");
    }
}

#[test]
fn a_union_inside_one_class_keeps_its_reason()
{
    let mut table = TermTable::default();
    let a = op(&mut table, Operation::from(0), &[]);
    let b = op(&mut table, Operation::from(1), &[]);
    let c = op(&mut table, Operation::from(2), &[]);
    let fa = op(&mut table, Operation::from(F), &[a]);
    let fc = op(&mut table, Operation::from(F), &[c]);
    let mut graph = EGraph::new(table, ());
    for term in [fa, fc] {
        let _class = graph.add(term).expect("a table term");
    }
    let ab = graph.equation(a, b).expect("a ground equation");
    let bc = graph.equation(b, c).expect("a ground equation");
    let ac = graph.equation(a, c).expect("a ground equation");
    let parents = graph.equation(fa, fc).expect("a ground equation");
    assert_eq!(graph.apply(ab, Vec::new()), Ok(Joined::Merged));
    assert_eq!(graph.apply(bc, Vec::new()), Ok(Joined::Merged));
    assert_eq!(graph.apply(ac, Vec::new()), Ok(Joined::Already));
    // The parents join by their own equation first, so their congruence is a
    // second union inside one class.
    assert_eq!(graph.apply(parents, Vec::new()), Ok(Joined::Merged));
    graph.rebuild().expect("a rebuild");
    assert_eq!(graph.redundant(), &[
        Redundant {
            left: a,
            right: c,
            reason: Reason::Input {
                equation: ac,
                direction: Direction::Forward,
                values: Vec::new(),
            },
        },
        Redundant {
            left: fa,
            right: fc,
            reason: Reason::Congruence,
        },
    ]);
    assert_eq!(graph.tally().unions, Count::from(3_usize));
}

#[test]
fn an_equation_that_cannot_match_is_refused_by_name()
{
    let mut table = TermTable::default();
    let x = var(&mut table, Variable::from(0));
    let y = var(&mut table, Variable::from(1));
    let a = op(&mut table, Operation::from(0), &[]);
    let fx = op(&mut table, Operation::from(F), &[x]);
    let fy = op(&mut table, Operation::from(F), &[y]);
    let mut graph = EGraph::new(table, ());
    let first = EquationPlace::from(0_usize);
    assert_eq!(graph.equation(x, a), Err(EGraphError::VariableLeft(first)));
    assert_eq!(
        graph.equation(fx, y),
        Err(EGraphError::Unbound(first, Variable::from(1_usize)))
    );
    assert_eq!(
        graph.equation(fy, a),
        Err(EGraphError::Values(first)),
        "the left side's variables skip the first place"
    );
    let open = graph.equation(fx, x).expect("an open equation");
    assert_eq!(
        graph.apply(open, Vec::new()),
        Err(EGraphError::Values(open))
    );
    let unknown = EquationPlace::from(9_usize);
    assert_eq!(
        graph.apply(unknown, vec![a]),
        Err(EGraphError::UnknownEquation(unknown))
    );
}
