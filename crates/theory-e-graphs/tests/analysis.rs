//! The analysis laws: each merge is a join, and after a rebuild each class
//! holds the join of its nodes' data.

use alloc::vec::Vec;

use gandr_theory_coherent_resolutions::Operation;
use gandr_theory_coherent_resolutions::TermPlace;
use gandr_theory_coherent_resolutions::TermSize;
use gandr_theory_coherent_resolutions::TermTable;
use gandr_theory_e_graphs::Analysis;
use gandr_theory_e_graphs::EGraph;
use gandr_theory_e_graphs::Growth;
use gandr_theory_e_graphs::Size;
use proptest::prelude::*;

use crate::fixtures::op;

/// The join of `left` and `right`, and whether it grows `left`.
///
/// # Specification
/// trivial.
fn join<A>(
    analysis: &A,
    left: &A::Data,
    right: &A::Data,
) -> (A::Data, Growth)
where
    A: Analysis,
{
    let mut into = left.clone();
    let growth = analysis.merge(&mut into, right.clone());
    (into, growth)
}

/// Whether `analysis`'s merge is the join of a semilattice on three data,
/// and reports its growth.
///
/// # Specification
/// trivial.
fn laws<A>(
    analysis: &A,
    [first, second, third]: [A::Data; 3],
) -> Result<(), TestCaseError>
where
    A: Analysis,
{
    let (both, growth) = join(analysis, &first, &second);
    prop_assert_eq!(&both, &join(analysis, &second, &first).0, "commutative");
    prop_assert_eq!(
        growth == Growth::Grew,
        both != first,
        "the growth is reported"
    );
    prop_assert_eq!(
        join(analysis, &both, &third).0,
        join(analysis, &first, &join(analysis, &second, &third).0).0,
        "associative"
    );
    prop_assert_eq!(
        join(analysis, &first, &first),
        (first, Growth::Stayed),
        "idempotent"
    );
    Ok(())
}

proptest! {
    #[test]
    fn the_merge_of_each_analysis_is_a_join(sizes in prop::array::uniform3(1_usize .. 64))
    {
        laws(&Size, sizes.map(TermSize::from))?;
    }
}

/// The operations of the random graphs: three constants, `f` of one
/// argument and `g` of two.
const F: usize = 3;
/// The operation `g`.
const G: usize = 4;

/// One step of a random term: its kind, and the indices of the earlier terms
/// that it takes as arguments.
#[derive(Clone, Copy, Debug)]
struct Step
{
    /// A constant, `f` or `g`, by its value modulo three.
    kind: u8,
    /// The index of the first argument, modulo the terms so far.
    first: usize,
    /// The index of the second argument, modulo the terms so far.
    second: usize,
}

/// The terms that `steps` build in order: a constant, or `f` or `g` over
/// earlier terms, each picked by its index modulo the terms so far.
///
/// # Specification
/// trivial.
fn terms(
    table: &mut TermTable,
    steps: &[Step],
) -> Vec<TermPlace>
{
    let mut built: Vec<TermPlace> = (0 .. F)
        .map(|constant| op(table, Operation::from(constant), &[]))
        .collect();
    for &Step {
        kind,
        first,
        second,
    } in steps
    {
        let pick = |index: usize| built[index.checked_rem(built.len()).expect("a built term")];
        let term = match kind % 3 {
            0 => op(table, Operation::from(F), &[pick(first)]),
            1 => op(table, Operation::from(G), &[pick(first), pick(second)]),
            _ => op(table, Operation::from(usize::from(kind) % F), &[]),
        };
        built.push(term);
    }
    built
}

proptest! {
    #[test]
    fn each_class_holds_the_join_of_its_nodes_data(
        steps in prop::collection::vec(
            (any::<u8>(), any::<usize>(), any::<usize>())
                .prop_map(|(kind, first, second)| Step { kind, first, second }),
            1 .. 24,
        ),
        equations in prop::collection::vec((any::<usize>(), any::<usize>()), 0 .. 8),
    )
    {
        // egg, § 4.1: after a rebuild, the datum of each class is the join of
        // `make` over its nodes.
        let mut table = TermTable::default();
        let built = terms(&mut table, &steps);
        let mut graph = EGraph::new(table, Size);
        for &term in &built {
            let _class = graph.add(term).expect("a table term");
        }
        for &(left, right) in &equations {
            let pick = |index: usize| built[index.checked_rem(built.len()).expect("a built term")];
            let (left, right) = (pick(left), pick(right));
            let equation = graph.equation(left, right).expect("a ground equation");
            let _joined = graph.apply(equation, Vec::new()).expect("an instance");
        }
        graph.rebuild().expect("a rebuild");
        let mut children: Vec<TermSize> = Vec::new();
        for class in graph.classes() {
            let mut joined: Option<TermSize> = None;
            for member in graph.members(class).expect("a held class") {
                let node = graph.table().node(member).expect("a table term");
                children.clear();
                children.extend(
                    node.children
                        .iter()
                        .map(|&child| *graph.data(child).expect("a held child")),
                );
                let made = Size.make(node.head, children.iter());
                joined = Some(joined.map_or(made, |so_far| join(&Size, &so_far, &made).0));
            }
            prop_assert_eq!(Some(*graph.data(class).expect("a held class")), joined);
        }
    }
}

#[test]
fn the_size_of_a_class_is_the_size_of_its_smallest_term()
{
    let mut table = TermTable::default();
    let a = op(&mut table, Operation::from(0), &[]);
    let b = op(&mut table, Operation::from(1), &[]);
    let fa = op(&mut table, Operation::from(F), &[a]);
    let ffa = op(&mut table, Operation::from(F), &[fa]);
    let gffa = op(&mut table, Operation::from(G), &[ffa, ffa]);
    let mut graph = EGraph::new(table, Size);
    for term in [gffa, b] {
        let _class = graph.add(term).expect("a table term");
    }
    let size = |graph: &EGraph<Size>, place| usize::from(*graph.data(place).expect("held"));
    assert_eq!(size(&graph, gffa), 7);
    let equation = graph.equation(ffa, b).expect("a ground equation");
    let _joined = graph.apply(equation, Vec::new()).expect("an instance");
    graph.rebuild().expect("a rebuild");
    assert_eq!(
        size(&graph, ffa),
        1,
        "`b` is the smallest term of its class"
    );
    assert_eq!(size(&graph, fa), 2);
    assert_eq!(
        size(&graph, gffa),
        3,
        "the parent's datum follows the repair"
    );
}
