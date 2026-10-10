//! The graph algorithms the precedence DAG and the closing-class derivation
//! stand on, over the dense [`EdgeSource`] boundary: cycle evidence,
//! reachability, and the strongly-connected-component condensation.
//!
//! Every algorithm validates its input once into sorted, deduplicated
//! adjacency rows, so a successor outside the node bound is a typed
//! [`GraphValidationError`] and never an index fault, and every result is in
//! canonical dense order, so it is independent of successor order and
//! duplicate edges.

use alloc::vec;
use alloc::vec::Vec;
use core::alloc::Layout;
use core::error::Error;
use core::fmt::Display;
use core::fmt::Formatter;
use core::fmt::Result as FmtResult;

use anodized::spec;
use petgraph::algo::condensation as petgraph_condensation;
use petgraph::graph::DefaultIx;
use petgraph::graph::DiGraph;
use petgraph::graph::IndexType;
use petgraph::graph::NodeIndex;

use crate::ComponentEdge;
use crate::ComponentIndex;
use crate::EdgeId;
use crate::NodeCount;
use crate::NodeId;
use crate::types::NodeCapacity;
use crate::types::NodePosition;

/// A directed graph over the dense nodes `0..node_count()`.
///
/// The one boundary every algorithm in the crate reads a graph through. It
/// names no storage, so a caller adapts whatever it holds, and no graph
/// library's type appears in it.
pub trait EdgeSource
{
    /// The iterator [`successors`](Self::successors) returns.
    type Successors<'successors>: Iterator<Item = NodeId> + 'successors
    where
        Self: 'successors;

    /// Reports the dense node bound.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the graph's nodes are exactly `0..node_count()`, and the
    ///   bound is the same on every call while the graph is unchanged.
    /// - panics: none.
    /// - executable: none — the bound's cross-call stability has no independent
    ///   representation observer on this required method; trait-wide checks
    ///   change the protocol every implementor must satisfy.
    ///
    /// # Adequacy
    /// - hypothesis: For stable dense-graph adapters, L3 named rows and L2
    ///   generated closure observations distinguish a wrong bound or omitted
    ///   node. These witnesses cover the in-crate adapter, not compliance of
    ///   arbitrary external implementations.
    /// - witness: `tests::algorithms::reachability_rows_on_a_named_graph`
    /// - witness: `tests::algorithms::reachability_agrees_with_the_closure_matrix`
    #[must_use]
    fn node_count(&self) -> NodeCount;

    /// Yields the targets of the edges leaving `node`.
    ///
    /// # Specification
    /// - requires: `node` is below [`node_count`](Self::node_count).
    /// - ensures: yields one target per outgoing edge, in any order and with
    ///   any repetition; a target outside the node bound is reported by the
    ///   algorithm that reads it as [`GraphValidationError::EdgeOutOfBounds`].
    /// - panics: none.
    /// - executable: none — a predicate on this declaration requires enclosing
    ///   trait instrumentation, which changes required methods in every
    ///   implementor; concrete adapters and algorithm observers are checked.
    ///
    /// # Adequacy
    /// - hypothesis: For valid sources in a stable adapter, L3 named graphs
    ///   observe direction, successor membership and malformed-target refusal;
    ///   L2 generated comparisons cover complete rows. Third-party iterator
    ///   stability and trait-protocol migration are outside these witnesses.
    /// - witness: `tests::algorithms::reachability_rows_on_a_named_graph`
    /// - witness: `tests::algorithms::out_of_bounds_edges_are_refused_by_name`
    /// - witness: `tests::algorithms::reachability_agrees_with_the_closure_matrix`
    fn successors(
        &self,
        node: NodeId,
    ) -> Self::Successors<'_>;
}

/// A graph the algorithms refuse, or a resource bound they cannot meet.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum GraphValidationError
{
    /// One slot per node does not fit the host's address space.
    NodeCountTooLarge
    {
        /// The refused node bound.
        node_count: NodeCount,
    },
    /// A caller-supplied node is not below the node bound.
    NodeOutOfBounds
    {
        /// The refused node.
        node: NodeId,
        /// The graph's node bound.
        node_count: NodeCount,
    },
    /// An edge targets a node that is not below the node bound.
    EdgeOutOfBounds
    {
        /// The edge's source.
        source: NodeId,
        /// The refused target.
        target: NodeId,
        /// The graph's node bound.
        node_count: NodeCount,
    },
    /// The edges do not fit the condensation's 32-bit edge indices.
    EdgeCountTooLarge,
    /// A checked conversion or count overflowed inside an algorithm.
    ArithmeticOverflow,
}

impl Display for GraphValidationError
{
    /// Writes the refusal with the values it names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut Formatter<'_>,
    ) -> FmtResult
    {
        match *self {
            | Self::NodeCountTooLarge { node_count } => {
                write!(f, "{node_count} nodes do not fit the address space")
            },
            | Self::NodeOutOfBounds { node, node_count } => {
                write!(f, "node {node} is outside 0..{node_count}")
            },
            | Self::EdgeOutOfBounds {
                source,
                target,
                node_count,
            } => write!(f, "edge {source}>{target} leaves 0..{node_count}"),
            | Self::EdgeCountTooLarge => f.write_str("the edges exceed the 32-bit edge indices"),
            | Self::ArithmeticOverflow => f.write_str("a graph algorithm's arithmetic overflowed"),
        }
    }
}

impl Error for GraphValidationError
{
}

/// A closed walk along graph edges: evidence that the graph has a cycle.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CycleWitness
{
    /// The walk's nodes; the first and last are the same node.
    pub nodes: Vec<NodeId>,
    /// The edges between consecutive nodes of the walk.
    pub edges: Vec<EdgeId>,
}

/// The nodes one source reaches.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReachabilityRow
{
    /// The source the row describes.
    pub source: NodeId,
    /// The nodes reachable from `source` by one or more edges, ascending;
    /// `source` itself is present exactly when a cycle passes through it.
    pub targets: Vec<NodeId>,
}

/// The transitive closure of a graph, one row per source.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Reachability
{
    /// One row per node, in ascending source order.
    pub rows: Vec<ReachabilityRow>,
}

/// A graph's strongly connected components and the acyclic graph between
/// them.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Condensation
{
    /// The components, each ascending, ordered by their smallest member; a
    /// component's position is its [`ComponentIndex`].
    pub components: Vec<Vec<NodeId>>,
    /// The edges between distinct components, ascending and without
    /// repetition.
    pub edges: Vec<ComponentEdge>,
}

/// Finds a cycle and returns it as a closed walk, or reports that there is
/// none.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `Ok(Some(witness))` exactly when the graph has a cycle, with
///   `witness.nodes` closed and every consecutive pair an edge of the graph;
///   `Ok(None)` exactly when the graph is acyclic.
/// - provides: deterministic evidence: the search visits roots in ascending
///   order and successors in ascending order, so the same graph yields the same
///   witness.
/// - fails: the graph's adjacency rows cannot be validated.
/// - panics: none.
/// - intension: an iterative three-colour depth-first search over the validated
///   rows; the first edge into an active node closes the witness.
///
/// # Errors
/// [`GraphValidationError::EdgeOutOfBounds`] for a successor outside the node
/// bound, [`GraphValidationError::NodeCountTooLarge`] when the rows do not fit
/// the address space.
///
/// # Adequacy
/// - hypothesis: For stable dense graphs, the predicate checks positive cycle
///   incidence and rejects a negative answer to a self-loop. L3 named
///   back-edge, self-loop and converging-path witnesses distinguish wrong
///   closure and false cycles; the deep chain observes iterative depth. L2
///   closure-matrix comparison supplies complete absence evidence, which the
///   bounded negative predicate deliberately does not recompute. Resource
///   exhaustion is outside those samples.
/// - witness: `tests::algorithms::cycle_witness_names_the_back_edge`
/// - witness: `tests::algorithms::deep_chain_runs_without_recursion`
/// - witness: `tests::algorithms::witness_exists_exactly_when_the_closure_has_a_loop`
#[spec(ensures: |ref result| match *result {
    Ok(Some(ref witness)) => witness.nodes.len() >= 2 && witness.nodes.first() == witness.nodes.last()
            && witness.edges.len().checked_add(1) == Some(witness.nodes.len())
            && witness.edges.iter().zip(witness.nodes.windows(2)).all(|(edge, pair)|
                matches!(*pair, [source, target] if edge.source == source && edge.target == target))
        && witness.edges.iter().all(|edge| u32::from(edge.source) < u32::from(graph.node_count())
            && graph.successors(edge.source).any(|target| target == edge.target)),
    Ok(None) => graph.node_count().ids().all(|source| !graph.successors(source).any(|target| target == source)),
    Err(GraphValidationError::EdgeOutOfBounds { source, target, node_count }) =>
            node_count == graph.node_count() && u32::from(source) < u32::from(node_count)
                && u32::from(target) >= u32::from(node_count)
                && graph.successors(source).any(|node| node == target),
        Err(GraphValidationError::NodeCountTooLarge { node_count }) => node_count == graph.node_count(),
    Err(_) => false,
})]
#[inline]
pub fn cycle_witness<G>(graph: &G) -> Result<Option<CycleWitness>, GraphValidationError>
where
    G: EdgeSource,
{
    let adjacency = adjacency_rows(graph)?;
    cycle_witness_from_rows(&adjacency, graph.node_count())
}

/// Computes the transitive closure: for each node, every node it reaches by
/// one or more edges.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one row per node in ascending source order; a row's targets are
///   ascending and are exactly the nodes reachable from its source by a
///   non-empty path, so the source appears in its own row exactly when it lies
///   on a cycle.
/// - fails: the graph's adjacency rows cannot be validated.
/// - panics: none.
/// - intension: one iterative depth-first traversal per source over the
///   validated rows, `O(n·(n + e))` in total, with one mark vector reused
///   across sources.
///
/// # Errors
/// [`GraphValidationError::EdgeOutOfBounds`] for a successor outside the node
/// bound, [`GraphValidationError::NodeCountTooLarge`] when the rows do not fit
/// the address space.
///
/// # Adequacy
/// - hypothesis: For stable dense graphs, the predicate observes dense sorted
///   rows, direct-edge inclusion and closure under another edge. L3 named rows
///   and refusal payloads distinguish omission, reversal and wrong bounds; L2
///   comparison with an independent matrix detects unreachable extras as well.
///   The predicate does not recompute leastness, and allocation failure is not
///   forced by the witnesses.
/// - witness: `tests::algorithms::reachability_rows_on_a_named_graph`
/// - witness: `tests::algorithms::out_of_bounds_edges_are_refused_by_name`
/// - witness: `tests::algorithms::reachability_agrees_with_the_closure_matrix`
#[spec(ensures: |ref result| match *result {
    Ok(ref reach) => usize::try_from(u32::from(graph.node_count())).is_ok_and(|count| reach.rows.len() == count)
        && reach.rows.iter().zip(graph.node_count().ids()).all(|(row, source)| row.source == source
            && row.targets.iter().all(|&target| u32::from(target) < u32::from(graph.node_count()))
            && row.targets.windows(2).all(|pair| matches!(*pair, [left, right] if left < right))
            && graph.successors(source).all(|target| row.targets.binary_search(&target).is_ok())
            && row.targets.iter().all(|&middle| graph.successors(middle)
                .all(|target| row.targets.binary_search(&target).is_ok()))),
    Err(GraphValidationError::EdgeOutOfBounds { source, target, node_count }) =>
            node_count == graph.node_count() && u32::from(source) < u32::from(node_count)
                && u32::from(target) >= u32::from(node_count)
                && graph.successors(source).any(|node| node == target),
        Err(GraphValidationError::NodeCountTooLarge { node_count }) => node_count == graph.node_count(),
    Err(_) => false,
})]
#[inline]
pub fn reachability<G>(graph: &G) -> Result<Reachability, GraphValidationError>
where
    G: EdgeSource,
{
    let adjacency = adjacency_rows(graph)?;
    let node_count = graph.node_count();
    let capacity = usize::from(node_capacity(node_count)?);
    let mut marked = vec![Mark::Unmarked; capacity];
    let mut stack = Vec::new();
    let mut rows = Vec::with_capacity(capacity);
    for source in node_count.ids() {
        let mut targets = Vec::new();
        let first = row_of(&adjacency, source, node_count)?;
        stack.extend_from_slice(first);
        while let Some(node) = stack.pop() {
            let slot = slot_of(&mut marked, node, node_count)?;
            if *slot == Mark::Marked {
                continue;
            }
            *slot = Mark::Marked;
            targets.push(node);
            let next = row_of(&adjacency, node, node_count)?;
            stack.extend_from_slice(next);
        }
        for &target in &targets {
            let slot = slot_of(&mut marked, target, node_count)?;
            *slot = Mark::Unmarked;
        }
        targets.sort_unstable();
        rows.push(ReachabilityRow { source, targets });
    }
    Ok(Reachability { rows })
}

/// Condenses each strongly connected component to one node and returns the
/// components with the acyclic graph between them.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the components partition the nodes; two nodes share a component
///   exactly when each reaches the other; components are ascending and ordered
///   by smallest member; `edges` holds `a>b` exactly when some input edge
///   leaves component `a` for a distinct component `b`, ascending and without
///   repetition.
/// - fails: the graph's adjacency rows cannot be validated, or its edges do not
///   fit 32-bit edge indices.
/// - panics: none.
/// - intension: the components come from petgraph's Kosaraju-based
///   `condensation` over an owned copy of the validated rows; the result is
///   then renumbered into canonical order, so petgraph's own component order is
///   never observed.
///
/// # Errors
/// [`GraphValidationError::EdgeOutOfBounds`] for a successor outside the node
/// bound, [`GraphValidationError::NodeCountTooLarge`] when the nodes exceed
/// the address space or the 32-bit node indices,
/// [`GraphValidationError::EdgeCountTooLarge`] when the edges exceed the
/// 32-bit edge indices.
///
/// # Adequacy
/// - hypothesis: For stable dense graphs, the predicate observes canonical
///   component rows, total membership, and input incidence of each reported
///   non-reflexive component edge. L3 named components and L2
///   mutual-reachability comparison distinguish merging, splitting, duplicate
///   membership and missing quotient edges. Exact partition and mutual
///   reachability remain oracle observations rather than a second SCC
///   computation; resource limits are not reached by these public-graph
///   samples.
/// - witness: `tests::algorithms::condensation_on_a_named_graph`
/// - witness: `tests::algorithms::condensation_agrees_with_mutual_reachability`
#[spec(ensures: |ref result| match *result {
    Ok(ref folded) => folded.components.iter().all(|members| !members.is_empty()
        && members.iter().all(|&node| u32::from(node) < u32::from(graph.node_count()))
        && members.windows(2).all(|pair| matches!(*pair, [left, right] if left < right)))
        && folded.components.iter().try_fold(0_usize, |total, members| total.checked_add(members.len()))
            .is_some_and(|total| u64::try_from(total).is_ok_and(|total| total == u64::from(u32::from(graph.node_count()))))
        && folded.components.iter().zip(folded.components.iter().skip(1))
            .all(|(left, right)| left.first() < right.first())
        && folded.edges.windows(2).all(|pair| matches!(*pair, [left, right] if left < right))
        && folded.edges.iter().all(|edge| edge.source != edge.target
            && usize::try_from(u32::from(edge.source)).ok().and_then(|index| folded.components.get(index))
                .zip(usize::try_from(u32::from(edge.target)).ok().and_then(|index| folded.components.get(index)))
                .is_some_and(|(sources, targets)| sources.iter().any(|&source| graph.successors(source)
                    .any(|target| targets.binary_search(&target).is_ok())))),
    Err(GraphValidationError::EdgeOutOfBounds { source, target, node_count }) =>
            node_count == graph.node_count() && u32::from(source) < u32::from(node_count)
                && u32::from(target) >= u32::from(node_count)
                && graph.successors(source).any(|node| node == target),
        Err(GraphValidationError::NodeCountTooLarge { node_count }) => node_count == graph.node_count(),
    Err(GraphValidationError::EdgeCountTooLarge) => true,
    Err(_) => false,
})]
#[inline]
pub fn condensation<G>(graph: &G) -> Result<Condensation, GraphValidationError>
where
    G: EdgeSource,
{
    let node_count = graph.node_count();
    let adjacency = adjacency_rows(graph)?;
    let owned = owned_graph::<DefaultIx>(&adjacency, node_count)?;
    let (condensed_nodes, condensed_edges) = petgraph_condensation(owned, false).into_nodes_edges();

    let mut ranked = Vec::with_capacity(condensed_nodes.len());
    for (position, node) in condensed_nodes.into_iter().enumerate() {
        let mut members = node.weight;
        members.sort_unstable();
        ranked.push((position, members));
    }
    ranked.sort_unstable_by_key(|component| component.1.first().copied());

    let mut public = vec![ComponentIndex::default(); ranked.len()];
    let mut canonical = Vec::with_capacity(ranked.len());
    for (rank, (position, members)) in ranked.into_iter().enumerate() {
        let raw =
            u32::try_from(rank).map_err(|_overflow| GraphValidationError::ArithmeticOverflow)?;
        let slot = public
            .get_mut(position)
            .ok_or(GraphValidationError::ArithmeticOverflow)?;
        *slot = ComponentIndex::from(raw);
        canonical.push(members);
    }

    let mut edges = Vec::new();
    for edge in condensed_edges {
        let source = public_index(&public, edge.source())?;
        let target = public_index(&public, edge.target())?;
        if source != target {
            edges.push(ComponentEdge::new(source, target));
        }
    }
    edges.sort_unstable();
    edges.dedup();
    Ok(Condensation {
        components: canonical,
        edges,
    })
}

/// Validates a graph into adjacency rows: one row per node, its targets
/// ascending and without repetition.
///
/// # Specification
/// - requires: nothing.
/// - ensures: on success the row at position `n` holds exactly the distinct
///   successors of node `n`, ascending, every one below the node bound.
/// - provides: the validated form every algorithm in the crate reads.
/// - fails: the first successor outside the node bound, in ascending source
///   order, or a node bound whose rows do not fit the address space.
/// - panics: none.
///
/// # Errors
/// [`GraphValidationError::EdgeOutOfBounds`] for a successor outside the node
/// bound, [`GraphValidationError::NodeCountTooLarge`] when the rows do not fit
/// the address space.
///
/// # Adequacy
/// - hypothesis: For stable dense adapters, the predicate compares both
///   directions of successor membership, canonical order and edge-refusal
///   provenance. L3 disorder, repetition and malformed-target witnesses
///   distinguish added or omitted edges and wrong source order. Allocation
///   refusal carries the requested bound but allocator behavior is not
///   reproduced.
/// - witness: `tests::algorithms::successor_permutations_preserve_all_observers`
/// - witness: `tests::algorithms::out_of_bounds_edges_are_refused_by_name`
#[spec(ensures: |ref result| match *result {
    Ok(ref rows) => usize::try_from(u32::from(graph.node_count())).is_ok_and(|count| rows.len() == count)
        && rows.iter().zip(graph.node_count().ids()).all(|(row, source)|
            row.windows(2).all(|pair| matches!(*pair, [left, right] if left < right))
            && row.iter().all(|&target| u32::from(target) < u32::from(graph.node_count())
                && graph.successors(source).any(|given| given == target))
            && graph.successors(source).all(|target| row.binary_search(&target).is_ok())),
    Err(GraphValidationError::EdgeOutOfBounds { source, target, node_count }) =>
        node_count == graph.node_count() && u32::from(source) < u32::from(node_count)
        && u32::from(target) >= u32::from(node_count)
        && graph.successors(source).any(|given| given == target)
        && node_count.ids().take_while(|&earlier| earlier < source)
            .all(|earlier| graph.successors(earlier).all(|given| u32::from(given) < u32::from(node_count))),
    Err(GraphValidationError::NodeCountTooLarge { node_count }) => node_count == graph.node_count(),
    Err(_) => false,
})]
fn adjacency_rows<G>(graph: &G) -> Result<Vec<Vec<NodeId>>, GraphValidationError>
where
    G: EdgeSource,
{
    let node_count = graph.node_count();
    let capacity = node_capacity(node_count)?;
    Layout::array::<Vec<NodeId>>(usize::from(capacity))
        .map_err(|_layout| GraphValidationError::NodeCountTooLarge { node_count })?;
    let mut rows = Vec::new();
    rows.try_reserve_exact(usize::from(capacity))
        .map_err(|_reserve| GraphValidationError::NodeCountTooLarge { node_count })?;
    for source in node_count.ids() {
        let mut row = Vec::new();
        for target in graph.successors(source) {
            if u32::from(target) >= u32::from(node_count) {
                return Err(GraphValidationError::EdgeOutOfBounds {
                    source,
                    target,
                    node_count,
                });
            }
            row.push(target);
        }
        row.sort_unstable();
        row.dedup();
        rows.push(row);
    }
    Ok(rows)
}

/// The search state of one node in [`cycle_witness_from_rows`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Colour
{
    /// Not yet reached.
    Unvisited,
    /// On the active search path.
    Active,
    /// Fully explored.
    Finished,
}

/// Whether [`reachability`]'s traversal from the current source has reached
/// a node.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Mark
{
    /// Not reached from the current source.
    Unmarked,
    /// Reached from the current source.
    Marked,
}

/// One frame of the iterative search: a node and the next successor to try.
#[derive(Clone, Copy, Debug)]
struct Frame
{
    /// The node under exploration.
    node: NodeId,
    /// The position of the next successor in the node's row.
    next: usize,
}

/// Finds the first cycle of an iterative depth-first search over validated
/// rows.
///
/// # Specification
/// - requires: `adjacency` came from [`adjacency_rows`] for a graph with
///   `node_count` nodes.
/// - ensures: as [`cycle_witness`].
/// - fails: only on an inconsistent stack or a row missing for a node below the
///   bound, neither of which validated rows produce.
/// - panics: none.
///
/// # Errors
/// [`GraphValidationError::ArithmeticOverflow`] on an inconsistent stack,
/// [`GraphValidationError::NodeOutOfBounds`] for a missing row.
///
/// # Adequacy
/// - hypothesis: For complete canonical adjacency rows, preconditions reject
///   missing rows, disorder and foreign targets; the positive observer checks
///   the returned closed walk against those rows. L3 back-edge and deep-chain
///   witnesses and L2 independent cycle-existence comparison distinguish
///   fabricated cycles and missed loops. Absence beyond self-loops is an oracle
///   boundary, not a duplicate traversal.
/// - witness: `tests::algorithms::cycle_witness_names_the_back_edge`
/// - witness: `tests::algorithms::deep_chain_runs_without_recursion`
/// - witness: `tests::algorithms::witness_exists_exactly_when_the_closure_has_a_loop`
#[spec(
    requires: usize::try_from(u32::from(node_count)).is_ok_and(|count| count == adjacency.len())
        && adjacency.iter().all(|row| row.iter().all(|&node| u32::from(node) < u32::from(node_count))
            && row.windows(2).all(|pair| matches!(*pair, [left, right] if left < right))),
    ensures: |ref result| match *result {
        Ok(Some(ref witness)) => witness.nodes.len() >= 2 && witness.nodes.first() == witness.nodes.last()
            && witness.edges.len().checked_add(1) == Some(witness.nodes.len())
            && witness.edges.iter().zip(witness.nodes.windows(2)).all(|(edge, pair)|
                matches!(*pair, [source, target] if edge.source == source && edge.target == target))
            && witness.edges.iter().all(|edge| usize::try_from(u32::from(edge.source)).ok()
                .and_then(|source| adjacency.get(source)).is_some_and(|row| row.contains(&edge.target))),
        Ok(None) => adjacency.iter().zip(node_count.ids()).all(|(row, source)| !row.contains(&source)),
        Err(_) => false,
    },
)]
fn cycle_witness_from_rows(
    adjacency: &[Vec<NodeId>],
    node_count: NodeCount,
) -> Result<Option<CycleWitness>, GraphValidationError>
{
    let capacity = node_capacity(node_count)?;
    let mut colours = vec![Colour::Unvisited; usize::from(capacity)];
    let mut path = Vec::<NodeId>::new();
    let mut frames = Vec::<Frame>::new();
    for root in node_count.ids() {
        let root_colour = slot_of(&mut colours, root, node_count)?;
        if *root_colour != Colour::Unvisited {
            continue;
        }
        *root_colour = Colour::Active;
        path.push(root);
        frames.push(Frame {
            node: root,
            next: 0,
        });
        while let Some(frame) = frames.last_mut() {
            let row = row_of(adjacency, frame.node, node_count)?;
            let Some(&target) = row.get(frame.next)
            else {
                let finished = frame.node;
                frames.pop();
                path.pop();
                let finished_colour = slot_of(&mut colours, finished, node_count)?;
                *finished_colour = Colour::Finished;
                continue;
            };
            frame.next = frame
                .next
                .checked_add(1)
                .ok_or(GraphValidationError::ArithmeticOverflow)?;
            let source = frame.node;
            let target_colour = slot_of(&mut colours, target, node_count)?;
            match *target_colour {
                | Colour::Unvisited => {
                    *target_colour = Colour::Active;
                    path.push(target);
                    frames.push(Frame {
                        node: target,
                        next: 0,
                    });
                },
                | Colour::Active => return Ok(Some(closed_walk(&path, source, target))),
                | Colour::Finished => {},
            }
        }
    }
    Ok(None)
}

/// Cuts the closed walk a back edge `source>target` makes out of the active
/// search path.
///
/// # Specification
/// - requires: `target` is on `path` and `source` is its last node.
/// - ensures: the walk runs from `target` along `path` to `source` and back to
///   `target`; its edges are the consecutive pairs.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: For a path containing the target and ending at the source, the
///   observer compares the returned suffix, closing node and every edge. L3
///   named back-edge and self-loop witnesses distinguish retaining an
///   irrelevant prefix, dropping the source or closing at another node. This
///   helper does not establish that the supplied path belongs to a graph.
/// - witness: `tests::algorithms::cycle_witness_names_the_back_edge`
#[spec(
    requires: path.contains(&target) && path.last() == Some(&source),
    ensures: |ref witness| witness.nodes.len() >= 2 && witness.nodes.first() == witness.nodes.last()
            && witness.edges.len().checked_add(1) == Some(witness.nodes.len())
            && witness.edges.iter().zip(witness.nodes.windows(2)).all(|(edge, pair)|
                matches!(*pair, [source, target] if edge.source == source && edge.target == target))
        && witness.nodes.last() == Some(&target)
        && witness.nodes.iter().take(witness.nodes.len().saturating_sub(1))
            .eq(path.iter().skip_while(|&&node| node != target)),
)]
fn closed_walk(
    path: &[NodeId],
    source: NodeId,
    target: NodeId,
) -> CycleWitness
{
    let start = path
        .iter()
        .position(|&node| node == target)
        .unwrap_or(path.len());
    let mut nodes = path.get(start ..).unwrap_or_default().to_vec();
    if nodes.last() != Some(&source) {
        nodes.push(source);
    }
    nodes.push(target);
    let edges = nodes
        .windows(2)
        .filter_map(|pair| match *pair {
            | [from, to] => Some(EdgeId::new(from, to)),
            | _ => None,
        })
        .collect();
    CycleWitness { nodes, edges }
}

/// Copies validated rows into an owned petgraph graph, node `n` at index `n`.
///
/// # Specification
/// - requires: `adjacency` came from [`adjacency_rows`] for a graph with
///   `node_count` nodes.
/// - ensures: the graph has node `n` at petgraph index `n`, weighted with `n`,
///   and one edge per row entry.
/// - fails: the nodes or edges exceed petgraph's 32-bit indices.
/// - panics: none; insertion goes through petgraph's fallible methods.
///
/// # Errors
/// [`GraphValidationError::NodeCountTooLarge`] for too many nodes,
/// [`GraphValidationError::EdgeCountTooLarge`] for too many edges.
///
/// # Adequacy
/// - hypothesis: For canonical complete rows, the predicate observes dense node
///   weights and the edge count; L3 named and L2 oracle condensations detect
///   incidence changes that counts alone miss. A small index representation
///   reaches both node and edge capacity refusals without exhausting memory.
///   Allocator failure is outside this evidence.
/// - witness: `tests::algorithms::condensation_on_a_named_graph`
/// - witness: `tests::algorithms::condensation_agrees_with_mutual_reachability`
/// - witness: `algorithms::tests::small_index_limits_remain_typed`
#[spec(
    requires: usize::try_from(u32::from(node_count)).is_ok_and(|count| count == adjacency.len())
        && adjacency.iter().all(|row| row.iter().all(|&node| u32::from(node) < u32::from(node_count))
            && row.windows(2).all(|pair| matches!(*pair, [left, right] if left < right))),
    ensures: |ref result| match *result {
        Ok(ref owned) => owned.node_weights().copied().eq(node_count.ids())
            && adjacency.iter().try_fold(0_usize, |total, row| total.checked_add(row.len())) == Some(owned.edge_count()),
        Err(GraphValidationError::NodeCountTooLarge { node_count: refused }) => refused == node_count,
        Err(GraphValidationError::EdgeCountTooLarge) => true,
        Err(_) => false,
    },
)]
fn owned_graph<Ix>(
    adjacency: &[Vec<NodeId>],
    node_count: NodeCount,
) -> Result<DiGraph<NodeId, (), Ix>, GraphValidationError>
where
    Ix: IndexType,
{
    let edge_count = adjacency.iter().map(Vec::len).sum();
    let mut graph = DiGraph::with_capacity(adjacency.len(), edge_count);
    for node in node_count.ids() {
        graph
            .try_add_node(node)
            .map_err(|_limit| GraphValidationError::NodeCountTooLarge { node_count })?;
    }
    for (source, row) in adjacency.iter().enumerate() {
        for &target in row {
            let target = usize::from(position_of(target, node_count)?);
            graph
                .try_add_edge(NodeIndex::new(source), NodeIndex::new(target), ())
                .map_err(|_limit| GraphValidationError::EdgeCountTooLarge)?;
        }
    }
    Ok(graph)
}

/// Looks up the public index of a condensed petgraph node.
///
/// # Specification
/// - requires: `public` names the canonical indices of known condensed nodes.
/// - ensures: returns the canonical index of `node`.
/// - fails: `node` is outside the map, which a condensation never produces.
/// - panics: none.
///
/// # Errors
/// [`GraphValidationError::ArithmeticOverflow`] for an unmapped index.
///
/// # Adequacy
/// - hypothesis: For an index map and any requested node, the result observer
///   distinguishes the mapped identity from a positional or zero fallback and
///   an absent entry from a successful lookup. L3 nonidentity and first-missing
///   witnesses pin both paths; constructing a globally correct permutation is
///   the caller boundary.
/// - witness: `algorithms::tests::canonical_indices_refuse_missing_positions`
#[spec(ensures: |ref result| match *result {
    Ok(index) => public.get(node.index()) == Some(&index),
    Err(GraphValidationError::ArithmeticOverflow) => public.get(node.index()).is_none(),
    Err(_) => false,
})]
fn public_index<Ix>(
    public: &[ComponentIndex],
    node: NodeIndex<Ix>,
) -> Result<ComponentIndex, GraphValidationError>
where
    Ix: IndexType,
{
    public
        .get(node.index())
        .copied()
        .ok_or(GraphValidationError::ArithmeticOverflow)
}

/// Widens a node bound to the length of a per-node vector.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the capacity equals the bound.
/// - fails: the bound does not fit `usize`.
/// - panics: none.
///
/// # Errors
/// [`GraphValidationError::NodeCountTooLarge`] when the bound does not fit.
///
/// # Adequacy
/// - hypothesis: For every node bound, L3 zero and largest-bound observations
///   distinguish a changed capacity or a wrong refusal payload. Refusal depends
///   on host address width; allocating that many rows is a separate operation
///   and is not claimed by this witness.
/// - witness: `algorithms::tests::bounds_and_slots_preserve_the_locus`
#[spec(ensures: |ref result| match *result {
    Ok(capacity) => u64::try_from(usize::from(capacity)).is_ok_and(|raw| raw == u64::from(u32::from(node_count))),
    Err(GraphValidationError::NodeCountTooLarge { node_count: refused }) => refused == node_count && usize::try_from(u32::from(node_count)).is_err(),
    Err(_) => false,
})]
fn node_capacity(node_count: NodeCount) -> Result<NodeCapacity, GraphValidationError>
{
    NodeCapacity::try_from(node_count)
        .map_err(|_overflow| GraphValidationError::NodeCountTooLarge { node_count })
}

/// Checks a node against the bound and widens it to a vector position.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the position equals the node.
/// - fails: the node is not below the bound.
/// - panics: none.
///
/// # Errors
/// [`GraphValidationError::NodeOutOfBounds`] for a node at or past the bound.
///
/// # Adequacy
/// - hypothesis: For any node and bound, the observer separates membership
///   refusal from host-width refusal and preserves the requested locus. L3
///   last-valid and first-invalid probes distinguish shifted bounds, truncation
///   and swapped payloads; narrow-host refusal remains conditional on the
///   target width.
/// - witness: `algorithms::tests::bounds_and_slots_preserve_the_locus`
#[spec(ensures: |ref result| match *result {
    Ok(position) => u32::from(node) < u32::from(node_count)
        && u64::try_from(usize::from(position)).is_ok_and(|raw| raw == u64::from(u32::from(node))),
    Err(GraphValidationError::NodeOutOfBounds { node: refused, node_count: bound }) =>
        refused == node && bound == node_count && u32::from(node) >= u32::from(node_count),
    Err(GraphValidationError::NodeCountTooLarge { node_count: bound }) =>
        bound == node_count && u32::from(node) < u32::from(node_count) && usize::try_from(u32::from(node)).is_err(),
    Err(_) => false,
})]
fn position_of(
    node: NodeId,
    node_count: NodeCount,
) -> Result<NodePosition, GraphValidationError>
{
    if u32::from(node) >= u32::from(node_count) {
        return Err(GraphValidationError::NodeOutOfBounds { node, node_count });
    }
    NodePosition::try_from(node)
        .map_err(|_overflow| GraphValidationError::NodeCountTooLarge { node_count })
}

/// Borrows one node's validated row.
///
/// # Specification
/// - requires: nothing.
/// - ensures: returns the row at the node's position.
/// - fails: the node is not below the bound or has no row.
/// - panics: none.
///
/// # Errors
/// [`GraphValidationError::NodeOutOfBounds`] for a node without a row.
///
/// # Adequacy
/// - hypothesis: For any rows, node and declared bound, the result observer
///   identifies the borrowed row and the exact refusal locus. L3 last-valid,
///   undeclared and declared-but-missing probes distinguish wrong indexing and
///   conflating the two bounds. The row contents themselves need not form a
///   validated graph.
/// - witness: `algorithms::tests::bounds_and_slots_preserve_the_locus`
#[spec(ensures: |ref result| match *result {
    Ok(row) => u32::from(node) < u32::from(node_count)
        && usize::try_from(u32::from(node)).ok().and_then(|position| adjacency.get(position))
            .is_some_and(|given| core::ptr::eq(core::ptr::from_ref(row), core::ptr::from_ref(given.as_slice()))),
    Err(GraphValidationError::NodeOutOfBounds { node: refused, node_count: bound }) =>
        refused == node && bound == node_count && (u32::from(node) >= u32::from(node_count)
            || usize::try_from(u32::from(node)).is_ok_and(|position| position >= adjacency.len())),
    Err(GraphValidationError::NodeCountTooLarge { node_count: bound }) => bound == node_count
        && u32::from(node) < u32::from(node_count) && usize::try_from(u32::from(node)).is_err(),
    Err(_) => false,
})]
fn row_of(
    adjacency: &[Vec<NodeId>],
    node: NodeId,
    node_count: NodeCount,
) -> Result<&[NodeId], GraphValidationError>
{
    let position = position_of(node, node_count)?;
    adjacency
        .get(usize::from(position))
        .map(Vec::as_slice)
        .ok_or(GraphValidationError::NodeOutOfBounds { node, node_count })
}

/// Borrows one node's slot in a per-node vector.
///
/// # Specification
/// - requires: nothing.
/// - ensures: returns the slot at the node's position.
/// - fails: the node is not below the bound or has no slot.
/// - panics: none.
///
/// # Errors
/// [`GraphValidationError::NodeOutOfBounds`] for a node without a slot.
///
/// # Adequacy
/// - hypothesis: For any slot slice, node and declared bound, the pointer
///   observer identifies the returned mutable slot, not merely an equal value.
///   L3 mutation of one slot and both bound refusals distinguish aliasing a
///   neighbour and changing the refusal locus. This does not validate the
///   values stored in the slice.
/// - witness: `algorithms::tests::bounds_and_slots_preserve_the_locus`
#[spec(
    captures: [length = slots.len(), expected = usize::try_from(u32::from(node)).ok()
        .and_then(|position| slots.get(position)).map(core::ptr::from_ref)],
    ensures: |ref result| match *result {
        Ok(ref slot) => u32::from(node) < u32::from(node_count) && expected == Some(core::ptr::from_ref(*slot)),
        Err(GraphValidationError::NodeOutOfBounds { node: refused, node_count: bound }) =>
            refused == node && bound == node_count && (u32::from(node) >= u32::from(node_count)
                || usize::try_from(u32::from(node)).is_ok_and(|position| position >= length)),
        Err(GraphValidationError::NodeCountTooLarge { node_count: bound }) => bound == node_count
            && u32::from(node) < u32::from(node_count) && usize::try_from(u32::from(node)).is_err(),
        Err(_) => false,
    },
)]
fn slot_of<T>(
    slots: &mut [T],
    node: NodeId,
    node_count: NodeCount,
) -> Result<&mut T, GraphValidationError>
{
    let position = position_of(node, node_count)?;
    slots
        .get_mut(usize::from(position))
        .ok_or(GraphValidationError::NodeOutOfBounds { node, node_count })
}

#[cfg(test)]
mod tests
{
    use super::*;

    #[test]
    fn bounds_and_slots_preserve_the_locus()
    {
        let bound = NodeCount::from(2);
        let last = NodeId::from(1);
        assert_eq!(position_of(last, bound), Ok(NodePosition::from(1)));
        assert_eq!(
            position_of(NodeId::from(2), bound),
            Err(GraphValidationError::NodeOutOfBounds {
                node: NodeId::from(2),
                node_count: bound
            })
        );
        let rows = vec![vec![NodeId::from(0)], vec![last]];
        assert_eq!(row_of(&rows, last, bound), Ok([last].as_slice()));
        assert_eq!(
            row_of(&rows[.. 1], last, bound),
            Err(GraphValidationError::NodeOutOfBounds {
                node: last,
                node_count: bound
            })
        );
        let mut slots = [10_u8, 20];
        *slot_of(&mut slots, last, bound).expect("last slot") = 23;
        assert_eq!(slots, [10, 23]);
        assert_eq!(
            slot_of(&mut slots, NodeId::from(2), bound),
            Err(GraphValidationError::NodeOutOfBounds {
                node: NodeId::from(2),
                node_count: bound
            })
        );
        assert_eq!(
            slot_of(&mut slots[.. 1], last, bound),
            Err(GraphValidationError::NodeOutOfBounds {
                node: last,
                node_count: bound
            })
        );
        assert_eq!(
            usize::from(node_capacity(NodeCount::from(0)).expect("zero capacity")),
            0
        );
        let maximum = NodeCount::from(u32::MAX);
        if let Ok(expected) = usize::try_from(u32::MAX) {
            assert_eq!(
                usize::from(node_capacity(maximum).expect("host capacity")),
                expected
            );
        }
        else {
            assert_eq!(
                node_capacity(maximum),
                Err(GraphValidationError::NodeCountTooLarge {
                    node_count: maximum
                })
            );
        }
    }

    #[test]
    fn canonical_indices_refuse_missing_positions()
    {
        let public = [
            ComponentIndex::from(2),
            ComponentIndex::from(0),
            ComponentIndex::from(1),
        ];
        assert_eq!(
            public_index(&public, NodeIndex::<u32>::new(1)),
            Ok(ComponentIndex::from(0))
        );
        assert_eq!(
            public_index(&public, NodeIndex::<u32>::new(3)),
            Err(GraphValidationError::ArithmeticOverflow)
        );
    }

    #[test]
    fn small_index_limits_remain_typed()
    {
        let fitting = vec![Vec::new(); 255];
        assert_eq!(
            owned_graph::<u8>(&fitting, NodeCount::from(255))
                .expect("last representable node count")
                .node_count(),
            255
        );
        let overflowing = vec![Vec::new(); 256];
        assert!(
            matches!(owned_graph::<u8>(&overflowing, NodeCount::from(256)), Err(GraphValidationError::NodeCountTooLarge { node_count }) if node_count == NodeCount::from(256))
        );
        let complete = vec![NodeCount::from(16).ids().collect::<Vec<_>>(); 16];
        assert!(matches!(
            owned_graph::<u8>(&complete, NodeCount::from(16)),
            Err(GraphValidationError::EdgeCountTooLarge)
        ));
    }
}
