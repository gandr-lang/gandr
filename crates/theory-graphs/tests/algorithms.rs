//! The graph algorithms: named graphs pinned row for row, refusals by name,
//! a deep chain that recursion would overflow, and generated graphs checked
//! against a closure-matrix oracle computed here, independently of the crate.

use core::error::Error;

use gandr_theory_graphs::ComponentEdge;
use gandr_theory_graphs::ComponentIndex;
use gandr_theory_graphs::EdgeSource;
use gandr_theory_graphs::GraphValidationError;
use gandr_theory_graphs::NodeCount;
use gandr_theory_graphs::NodeId;
use gandr_theory_graphs::condensation;
use gandr_theory_graphs::cycle_witness;
use gandr_theory_graphs::reachability;
use proptest::prelude::*;

/// A fixture graph: a node bound and one successor list per node, kept as
/// given, so duplicates and disorder reach the algorithms.
#[derive(Clone, Debug)]
struct TestGraph
{
    /// The node bound.
    node_count: NodeCount,
    /// The successors of each node, in insertion order.
    rows: Vec<Vec<NodeId>>,
}

/// One fixture edge, from a raw source to a raw target.
#[derive(Clone, Copy, Debug)]
struct RawEdge(u32, u32);

impl From<(u32, u32)> for RawEdge
{
    /// Wraps a raw pair.
    ///
    /// # Specification
    /// trivial.
    fn from(value: (u32, u32)) -> Self
    {
        Self(value.0, value.1)
    }
}

impl TestGraph
{
    /// Builds a graph of `node_count` nodes from raw edges; an edge from a
    /// source past the bound is dropped, an edge to a target past it kept.
    ///
    /// # Specification
    /// trivial.
    fn new<N, E>(
        node_count: N,
        edges: &[E],
    ) -> Self
    where
        N: Into<NodeCount>,
        E: Copy + Into<RawEdge>,
    {
        let node_count = node_count.into();
        let mut rows = vec![Vec::new(); usize::try_from(u32::from(node_count)).expect("fits")];
        for &edge in edges {
            let RawEdge(source, target) = edge.into();
            if let Some(row) = rows.get_mut(usize::try_from(source).expect("fits")) {
                row.push(NodeId::from(target));
            }
        }
        Self { node_count, rows }
    }
}

impl EdgeSource for TestGraph
{
    type Successors<'successors>
        = core::iter::Copied<core::slice::Iter<'successors, NodeId>>
    where
        Self: 'successors;

    /// Reports the bound.
    ///
    /// # Specification
    /// trivial.
    fn node_count(&self) -> NodeCount
    {
        self.node_count
    }

    /// Yields a node's successors as given.
    ///
    /// # Specification
    /// trivial.
    fn successors(
        &self,
        node: NodeId,
    ) -> Self::Successors<'_>
    {
        self.rows[usize::try_from(u32::from(node)).expect("fits")]
            .iter()
            .copied()
    }
}

/// Whether the oracle found a non-empty path between two nodes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Reach
{
    /// No non-empty path.
    Unreached,
    /// A non-empty path.
    Reached,
}

/// The transitive closure as a matrix, by Warshall's algorithm over the raw
/// rows: `closure[a][b]` is [`Reach::Reached`] exactly when a non-empty path
/// leads from `a` to `b`.
///
/// # Specification
/// trivial.
fn closure_matrix(graph: &TestGraph) -> Vec<Vec<Reach>>
{
    let size = graph.rows.len();
    let mut closure = vec![vec![Reach::Unreached; size]; size];
    for (source, row) in graph.rows.iter().enumerate() {
        for &target in row {
            closure[source][usize::try_from(u32::from(target)).expect("fits")] = Reach::Reached;
        }
    }
    for middle in 0 .. size {
        let through = closure[middle].clone();
        for row in &mut closure {
            if row[middle] == Reach::Reached {
                for (reach, &onward) in row.iter_mut().zip(&through) {
                    if onward == Reach::Reached {
                        *reach = Reach::Reached;
                    }
                }
            }
        }
    }
    closure
}

/// Wraps raw ids.
///
/// # Specification
/// trivial.
fn ids<R>(raw: &[R]) -> Vec<NodeId>
where
    R: Copy + Into<NodeId>,
{
    raw.iter().copied().map(Into::into).collect()
}

/// Names the node at a vector position.
///
/// # Specification
/// trivial.
fn node_at<P>(position: P) -> NodeId
where
    P: TryInto<u32>,
{
    NodeId::from(position.try_into().ok().expect("fits"))
}

/// The strategy for a graph of six nodes and up to eighteen edges, self
/// loops and repeats included.
///
/// # Specification
/// trivial.
fn small_graphs() -> impl Strategy<Value = TestGraph>
{
    proptest::collection::vec((0_u32 .. 6, 0_u32 .. 6), 0 .. 18)
        .prop_map(|edges| TestGraph::new(6_u32, &edges))
}

#[test]
fn out_of_bounds_edges_are_refused_by_name()
{
    let graph = TestGraph::new(2_u32, &[(0, 1), (1, 2)]);
    let refusal = GraphValidationError::EdgeOutOfBounds {
        source: NodeId::from(1),
        target: NodeId::from(2),
        node_count: NodeCount::from(2),
    };
    assert_eq!(Err(refusal.clone()), reachability(&graph));
    assert_eq!(Err(refusal.clone()), cycle_witness(&graph));
    assert_eq!(Err(refusal), condensation(&graph));
}

#[test]
fn reachability_rows_on_a_named_graph() -> Result<(), Box<dyn Error>>
{
    let graph = TestGraph::new(6_u32, &[(0, 2), (0, 1), (1, 3), (2, 3), (3, 4)]);
    let rows = reachability(&graph)?
        .rows
        .into_iter()
        .map(|row| (row.source, row.targets))
        .collect::<Vec<_>>();
    assert_eq!(
        vec![
            (node_at(0_u32), ids(&[1_u32, 2, 3, 4])),
            (node_at(1_u32), ids(&[3_u32, 4])),
            (node_at(2_u32), ids(&[3_u32, 4])),
            (node_at(3_u32), ids(&[4_u32])),
            (node_at(4_u32), vec![]),
            (node_at(5_u32), vec![]),
        ],
        rows
    );

    let looped = TestGraph::new(3_u32, &[(0, 1), (1, 0), (1, 2)]);
    let rows = reachability(&looped)?
        .rows
        .into_iter()
        .map(|row| row.targets)
        .collect::<Vec<_>>();
    assert_eq!(
        vec![ids(&[0_u32, 1, 2]), ids(&[0_u32, 1, 2]), vec![]],
        rows,
        "a node on a cycle reaches itself; a node off every cycle does not"
    );
    Ok(())
}

#[test]
fn condensation_on_a_named_graph() -> Result<(), Box<dyn Error>>
{
    let graph = TestGraph::new(6_u32, &[
        (3, 4),
        (2, 3),
        (3, 2),
        (1, 2),
        (0, 1),
        (1, 0),
        (1, 2),
        (0, 3),
    ]);
    let condensed = condensation(&graph)?;
    assert_eq!(
        vec![
            ids(&[0_u32, 1]),
            ids(&[2_u32, 3]),
            ids(&[4_u32]),
            ids(&[5_u32])
        ],
        condensed.components
    );
    assert_eq!(
        vec![
            ComponentEdge::new(ComponentIndex::from(0), ComponentIndex::from(1)),
            ComponentEdge::new(ComponentIndex::from(1), ComponentIndex::from(2)),
        ],
        condensed.edges
    );
    Ok(())
}

#[test]
fn cycle_witness_names_the_back_edge() -> Result<(), Box<dyn Error>>
{
    let graph = TestGraph::new(4_u32, &[(0, 1), (1, 2), (2, 1), (2, 3)]);
    let witness = cycle_witness(&graph)?.expect("the graph has a cycle");
    assert_eq!(ids(&[1_u32, 2, 1]), witness.nodes);
    assert_eq!(
        vec![
            (node_at(1_u32), node_at(2_u32)),
            (node_at(2_u32), node_at(1_u32))
        ],
        witness
            .edges
            .iter()
            .map(|edge| (edge.source, edge.target))
            .collect::<Vec<_>>()
    );

    let self_loop = TestGraph::new(2_u32, &[(0, 1), (1, 1)]);
    let witness = cycle_witness(&self_loop)?.expect("a self loop is a cycle");
    assert_eq!(ids(&[1_u32, 1]), witness.nodes);

    let diamond = TestGraph::new(4_u32, &[(0, 1), (0, 2), (1, 3), (2, 3)]);
    assert_eq!(
        None,
        cycle_witness(&diamond)?,
        "converging paths are not a cycle"
    );
    Ok(())
}

#[test]
fn deep_chain_runs_without_recursion() -> Result<(), Box<dyn Error>>
{
    let length = 20_000_u32;
    let edges = (1 .. length)
        .map(|target| (target.checked_sub(1).expect("target is positive"), target))
        .collect::<Vec<_>>();
    let graph = TestGraph::new(length, &edges);
    assert_eq!(None, cycle_witness(&graph)?);
    let condensed = condensation(&graph)?;
    assert_eq!(
        usize::try_from(length)?,
        condensed.components.len(),
        "every node of a chain is its own component"
    );
    assert_eq!(
        usize::try_from(length.checked_sub(1).expect("length is positive"))?,
        condensed.edges.len()
    );
    Ok(())
}

proptest! {
    #[test]
    fn reachability_agrees_with_the_closure_matrix(graph in small_graphs()) {
        let closure = closure_matrix(&graph);
        let rows = reachability(&graph).expect("generated edges are in bounds").rows;
        for (source, row) in rows.into_iter().enumerate() {
            prop_assert_eq!(node_at(source), row.source);
            let expected = closure[source]
                .iter()
                .enumerate()
                .filter(|&(_, &reach)| reach == Reach::Reached)
                .map(|(target, _)| node_at(target))
                .collect::<Vec<_>>();
            prop_assert_eq!(expected, row.targets);
        }
    }

    #[test]
    fn witness_exists_exactly_when_the_closure_has_a_loop(graph in small_graphs()) {
        let closure = closure_matrix(&graph);
        let cyclic = (0 .. closure.len()).any(|node| closure[node][node] == Reach::Reached);
        let witness = cycle_witness(&graph).expect("generated edges are in bounds");
        prop_assert_eq!(cyclic, witness.is_some());
        if let Some(witness) = witness {
            prop_assert!(witness.nodes.len() >= 2);
            prop_assert_eq!(witness.nodes.first(), witness.nodes.last());
            prop_assert_eq!(witness.edges.len().checked_add(1), Some(witness.nodes.len()));
            let successors = witness.nodes.iter().skip(1);
            for ((&from, &to), edge) in witness.nodes.iter().zip(successors).zip(&witness.edges) {
                prop_assert_eq!((from, to), (edge.source, edge.target));
                let source = usize::try_from(u32::from(edge.source)).expect("fits");
                prop_assert!(graph.rows[source].contains(&edge.target));
            }
        }
    }

    #[test]
    fn condensation_agrees_with_mutual_reachability(graph in small_graphs()) {
        let closure = closure_matrix(&graph);
        let condensed = condensation(&graph).expect("generated edges are in bounds");
        let size = closure.len();
        let mut component_of = vec![None; size];
        let mut previous_first = None;
        for (index, component) in condensed.components.iter().enumerate() {
            prop_assert!(!component.is_empty());
            prop_assert!(component.iter().zip(component.iter().skip(1)).all(|(low, high)| low < high));
            prop_assert!(previous_first < component.first().copied());
            previous_first = component.first().copied();
            for &node in component {
                let node = usize::try_from(u32::from(node)).expect("fits");
                prop_assert_eq!(None, component_of[node], "components are disjoint");
                component_of[node] = Some(index);
            }
        }
        let component_of = component_of
            .into_iter()
            .collect::<Option<Vec<_>>>()
            .expect("components cover every node");
        for left in 0 .. size {
            for right in 0 .. size {
                let mutual = left == right
                    || (closure[left][right] == Reach::Reached && closure[right][left] == Reach::Reached);
                prop_assert_eq!(mutual, component_of[left] == component_of[right]);
            }
        }
        let mut expected_edges = Vec::new();
        for (source, row) in graph.rows.iter().enumerate() {
            for &target in row {
                let target = usize::try_from(u32::from(target)).expect("fits");
                let (from, to) = (component_of[source], component_of[target]);
                if from != to {
                    expected_edges.push(ComponentEdge::new(
                        ComponentIndex::from(u32::try_from(from).expect("fits")),
                        ComponentIndex::from(u32::try_from(to).expect("fits")),
                    ));
                }
            }
        }
        expected_edges.sort_unstable();
        expected_edges.dedup();
        prop_assert_eq!(expected_edges, condensed.edges);
    }
}
