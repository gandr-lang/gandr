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
/// - hypothesis: L3 pointwise plus L1 evidence — a back edge inside a longer
///   path yields exactly the two-node closed walk; a 20 000-node chain yields
///   none without native recursion; generated graphs agree with a
///   closure-matrix oracle on whether a cycle exists, and every witness is
///   checked as a closed walk over input edges.
/// - witness: `tests::algorithms::cycle_witness_names_the_back_edge`
/// - witness: `tests::algorithms::deep_chain_runs_without_recursion`
/// - witness: `tests::algorithms::witness_exists_exactly_when_the_closure_has_a_loop`
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
/// - hypothesis: L3 pointwise plus L2 generative — a named diamond-and-tail
///   graph pins every row, an out-of-bounds edge pins the refusal, and
///   generated graphs agree row for row with a closure-matrix oracle.
/// - witness: `tests::algorithms::reachability_rows_on_a_named_graph`
/// - witness: `tests::algorithms::out_of_bounds_edges_are_refused_by_name`
/// - witness: `tests::algorithms::reachability_agrees_with_the_closure_matrix`
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
/// - hypothesis: L3 pointwise plus L2 generative — a named graph of two
///   two-node cycles, a tail and an isolated node pins the components and the
///   deduplicated edges; generated graphs agree with a closure-matrix oracle on
///   the partition and on the component edges.
/// - witness: `tests::algorithms::condensation_on_a_named_graph`
/// - witness: `tests::algorithms::condensation_agrees_with_mutual_reachability`
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
/// - requires: `public` maps every condensed index to its canonical index.
/// - ensures: returns the canonical index of `node`.
/// - fails: `node` is outside the map, which a condensation never produces.
/// - panics: none.
///
/// # Errors
/// [`GraphValidationError::ArithmeticOverflow`] for an unmapped index.
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
