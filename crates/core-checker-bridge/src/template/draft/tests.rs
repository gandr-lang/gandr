use gandr_kernel_term::stage::Index;
use gandr_kernel_term::stage::Term;

use super::*;

/// The graph classifier a code's imported node carries.
///
/// # Specification
/// trivial.
fn coded(
    graph: &Graph,
    id: Id,
) -> TypeId
{
    let Head::Code(ty) = graph.node(id).unwrap().head
    else {
        panic!("a code imports as a code");
    };
    ty
}

/// A remembered verdict answers only for its own pair: a pair matching
/// another remembered pair at one side is compared afresh, and an arrow
/// agrees with an equal arrow through its domain and codomain.
#[test]
fn a_remembered_classifier_verdict_answers_only_for_its_pair()
{
    let mut arena = Arena::default();
    let nat = arena.alloc_type(Type::Nat(Stage::Outer)).unwrap();
    let arrow = arena.alloc_type(Type::Arrow(nat, nat)).unwrap();
    let codes = [nat, arrow].map(|ty| arena.alloc(Term::Code(ty)).unwrap());
    let mut graph = Graph::default();
    let roots = graph.import(&arena, &codes).unwrap();
    let [pattern_nat, pattern_arrow] = [roots[0], roots[1]].map(|id| coded(&graph, id));
    let mut stack = Vec::new();
    let mut known = Vec::from([
        (pattern_arrow, nat, Agreement::Different),
        (pattern_nat, arrow, Agreement::Different),
    ]);
    assert_eq!(
        classifiers_agree(&graph, pattern_arrow, &arena, arrow, &mut stack, &mut known),
        Ok(Agreement::Equal),
        "{known:?}"
    );
    assert_eq!(
        known.last(),
        Some(&(pattern_arrow, arrow, Agreement::Equal)),
        "the fresh verdict is remembered"
    );
}

/// A graph is compact exactly when its roots reach every node: a node two
/// edges share is reached once, and a node no root reaches is garbage.
#[test]
fn a_graph_is_compact_exactly_when_its_roots_reach_every_node()
{
    let mut arena = Arena::default();
    let variable = arena.alloc(Term::Variable(Index(0))).unwrap();
    let applied = arena.alloc(Term::Apply(variable, variable)).unwrap();
    let mut graph = Graph::default();
    let roots = graph.import(&arena, &[variable, applied]).unwrap();
    let mut drafter = Drafter::default();
    assert_eq!(
        tidiness(&graph, &roots[1 ..], &mut drafter),
        Ok(Tidiness::Compact),
        "the application reaches its shared argument"
    );
    assert_eq!(
        tidiness(&graph, &roots[.. 1], &mut drafter),
        Ok(Tidiness::Garbage),
        "the variable alone leaves the application unreached"
    );
}
