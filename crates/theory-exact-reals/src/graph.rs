//! A plan read as a graph, and the Morse matching that isolates its recursive
//! core.
//!
//! A [`PlanGraph`] holds the [`Label`] of each node and its operands in order.
//! A label is the node's own bytes without its children, and it states
//! whether the order of the operands counts. The sum, the product, the meet
//! and the join take their operands unordered. A plan has no cycle, but a
//! [`GraphBuilder`] also writes a recursive system such as `x = 2^-x`, whose
//! nodes name each other.
//!
//! [`PlanGraph::core`] reads the graph as a complex of dimension one: each
//! node is a vertex, and each operand is an edge. It matches each node of the
//! well-founded part that has operands with an edge to an operand one rank
//! down, and `theory-discrete-morse` checks the matching. Each gradient path
//! ends at a leaf. The nodes with operands that stay critical are the
//! recursive core, and the core of a plan is empty.
//!
//! # Items
//!
//! - [`PlanGraph`], [`GraphBuilder`], [`GraphNode`], [`GraphError`] — the
//!   graph, its builder, a node, and the refusals.
//! - [`Label`], [`LabelBytes`], [`Operands`] — the label of a node.
//! - [`Core`] — the recursive core, and the faults of its matching.
//!
//! # References
//!
//! - `Doré-2023-computing_spaces_type_theory` — exemplar: § 3.4 states a
//!   matching of a graph as a function whose fixed points are the critical
//!   vertices, and its acyclicity as a gradient path from each vertex to a
//!   critical vertex. Example 3.8 collapses an infinite graph along such a
//!   matching. Maximilian Doré, "Computing Spaces in Type Theory", doctoral
//!   thesis, University of Oxford, 2023.

use alloc::vec::Vec;
use core::convert::Infallible;
use core::fmt;
use core::hash::BuildHasher as _;

use foldhash::fast::FixedState;
use gandr_theory_discrete_morse::Budget;
use gandr_theory_discrete_morse::Class;
use gandr_theory_discrete_morse::Complex;
use gandr_theory_discrete_morse::Faults;
use gandr_theory_discrete_morse::Incidence;
use gandr_theory_discrete_morse::MorseError;
use gandr_theory_discrete_morse::Scheme;
use gandr_theory_discrete_morse::Standing;
use gandr_theory_discrete_morse::collapse;
use hashbrown::HashTable;

use crate::codec::Entry;
use crate::minimal::MinimalForm;
use crate::minimal::minimal;
use crate::plan::Node;
use crate::plan::NodeCount;
use crate::plan::NodeId;
use crate::plan::Open;
use crate::plan::Plan;
use crate::plan::Real;

/// A node of a plan graph: its position in the graph, or in the builder that
/// writes the graph.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct GraphNode(u32);

impl From<NodeId> for GraphNode
{
    /// The node of a plan's graph at the plan's position `id`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(id: NodeId) -> Self
    {
        return Self(u32::from(id));
    }
}

impl From<u32> for GraphNode
{
    /// The node at `position`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: u32) -> Self
    {
        return Self(position);
    }
}

impl From<GraphNode> for u32
{
    /// The position as a number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(node: GraphNode) -> Self
    {
        return node.0;
    }
}

impl From<GraphNode> for usize
{
    /// The position as an index, or `usize::MAX` past the indices.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(node: GraphNode) -> Self
    {
        return Self::try_from(node.0).unwrap_or(Self::MAX);
    }
}

/// Whether the order of a node's operands counts.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Operands
{
    /// Two nodes are alike only when their operands are alike position by
    /// position.
    Ordered,
    /// Two nodes are alike when their operands are alike as multisets.
    Unordered,
}

/// The bytes of a label, borrowed.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct LabelBytes<'bytes>(&'bytes [u8]);

impl<'bytes> From<&'bytes [u8]> for LabelBytes<'bytes>
{
    /// Read `bytes` as the bytes of a label.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: &'bytes [u8]) -> Self
    {
        return Self(bytes);
    }
}

/// The label of a node: its own bytes, without its children, and whether the
/// order of its operands counts. Labels order by their bytes first.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Label
{
    /// The bytes.
    bytes: Vec<u8>,
    /// Whether the order of the operands counts.
    operands: Operands,
}

impl Label
{
    /// The label of `bytes` whose operands take the order `operands`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new(
        bytes: LabelBytes<'_>,
        operands: Operands,
    ) -> Self
    {
        return Self {
            bytes: bytes.0.to_vec(),
            operands,
        };
    }

    /// Whether the order of the operands counts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn operands(&self) -> Operands
    {
        return self.operands;
    }
}

impl AsRef<[u8]> for Label
{
    /// Borrow the bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        return &self.bytes;
    }
}

/// A refused graph operation.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum GraphError
{
    /// A node names a position that holds no node.
    UnknownNode,
    /// The builder holds a node that no label and no operands define.
    Undefined,
    /// The node is defined already.
    Redefined,
    /// An ordered node has more than 64 operands.
    Wide,
    /// The graph holds more nodes or operands than a position counts.
    TooManyNodes,
    /// The root does not reach the node.
    Unreached,
}

impl fmt::Display for GraphError
{
    /// Write the refusal as one line.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let line = match *self {
            Self::UnknownNode => "a node names a position that holds no node",
            Self::Undefined => "the builder holds a node with no label and no operands",
            Self::Redefined => "the node is defined already",
            Self::Wide => "an ordered node has more than 64 operands",
            Self::TooManyNodes => "the graph holds more nodes than a position counts",
            Self::Unreached => "the root does not reach the node",
        };
        return f.write_str(line);
    }
}

impl core::error::Error for GraphError
{
}

/// The label and the operands of one node of a builder.
#[derive(Clone, Copy, Debug)]
struct Slot
{
    /// The label's place in the builder's labels.
    label: LabelPlace,
    /// Where the node's operands start.
    start: u32,
    /// Where the node's operands end.
    end: u32,
}

/// The distinct labels of a graph in the order of their first use, each
/// found by its bytes and its order of operands. A label is allocated once,
/// when it is new.
#[derive(Clone, Debug, Default)]
struct Labels
{
    /// The labels, each at its place.
    held: Vec<Label>,
    /// The place of each label, hashed by its bytes and its order.
    places: HashTable<u32>,
    /// The hasher of the places.
    state: FixedState,
}

impl Labels
{
    /// The place of the label of `bytes` and `operands`, or none when the
    /// table holds no such label.
    ///
    /// # Specification
    /// trivial.
    fn find(
        &self,
        bytes: LabelBytes<'_>,
        operands: Operands,
    ) -> Option<LabelPlace>
    {
        let hash = self.state.hash_one((bytes.0, operands));
        let labels = &self.held;
        return self
            .places
            .find(hash, |&place| {
                return usize::try_from(place)
                    .ok()
                    .and_then(|at| labels.get(at))
                    .is_some_and(|label| label.bytes == bytes.0 && label.operands == operands);
            })
            .copied()
            .map(LabelPlace);
    }

    /// Hold `label`, which the table does not hold yet, at the next place.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`GraphError::TooManyNodes`]: the places pass the 32-bit range.
    fn insert(
        &mut self,
        label: Label,
    ) -> Result<LabelPlace, GraphError>
    {
        let place = u32::try_from(self.held.len()).map_err(|_full| GraphError::TooManyNodes)?;
        let hash = self
            .state
            .hash_one((label.bytes.as_slice(), label.operands));
        self.held.push(label);
        let (labels, state) = (&self.held, &self.state);
        let _entry = self.places.insert_unique(hash, place, |&held| {
            return usize::try_from(held)
                .ok()
                .and_then(|at| labels.get(at))
                .map_or(0, |label| {
                    state.hash_one((label.bytes.as_slice(), label.operands))
                });
        });
        return Ok(LabelPlace(place));
    }
}

/// The writer of a plan graph whose nodes may name each other in any order,
/// so a graph with cycles: reserve a node, then define it.
#[derive(Clone, Debug, Default)]
pub struct GraphBuilder
{
    /// The distinct labels.
    labels: Labels,
    /// Each node's label and operands, or nothing before its definition.
    nodes: Vec<Option<Slot>>,
    /// The operands of every node, each node's in one run.
    operands: Vec<GraphNode>,
}

impl GraphBuilder
{
    /// An empty builder.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        return Self::default();
    }

    /// A new node, not yet defined.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// - [`GraphError::TooManyNodes`]: no position counts another node.
    #[inline]
    pub fn reserve(&mut self) -> Result<GraphNode, GraphError>
    {
        let position = u32::try_from(self.nodes.len()).map_err(|_full| GraphError::TooManyNodes)?;
        self.nodes.push(None);
        return Ok(GraphNode(position));
    }

    /// Define the reserved `node` by its label and its operands, which may
    /// name any node of the builder, `node` too.
    ///
    /// # Specification
    /// - ensures: the node holds `label` and `operands`, in order.
    /// - fails: refuses a node that the builder does not hold, a node that is
    ///   defined already, and an ordered node with more than 64 operands. The
    ///   builder stays as it was.
    /// - panics: none.
    /// - executable: none — the clause restates the definition.
    ///
    /// # Errors
    /// - [`GraphError::UnknownNode`]: the builder holds no node at `node`.
    /// - [`GraphError::Redefined`]: the node is defined already.
    /// - [`GraphError::Wide`]: an ordered node has more than 64 operands.
    /// - [`GraphError::TooManyNodes`]: no position counts the operands.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a foreign node, a second definition and 65 ordered
    ///   operands are each refused by name.
    /// - witness: `tests::minimal::the_builder_refuses_by_name`
    #[inline]
    pub fn define(
        &mut self,
        node: GraphNode,
        label: Label,
        operands: &[GraphNode],
    ) -> Result<(), GraphError>
    {
        match self.nodes.get(usize::from(node)) {
            None => return Err(GraphError::UnknownNode),
            Some(&Some(_)) => return Err(GraphError::Redefined),
            Some(&None) => {},
        }
        if label.operands == Operands::Ordered && operands.len() > 64 {
            return Err(GraphError::Wide);
        }
        let start = u32::try_from(self.operands.len()).map_err(|_full| GraphError::TooManyNodes)?;
        let end = u32::try_from(self.operands.len().saturating_add(operands.len()))
            .map_err(|_full| GraphError::TooManyNodes)?;
        let held = self.labels.find(LabelBytes(&label.bytes), label.operands);
        let place = held.map_or_else(|| self.labels.insert(label), Ok)?;
        self.operands.extend_from_slice(operands);
        if let Some(slot) = self.nodes.get_mut(usize::from(node)) {
            *slot = Some(Slot {
                label: place,
                start,
                end,
            });
        }
        return Ok(());
    }

    /// A new node, defined at once by its label and its operands.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// As [`Self::reserve`] and [`Self::define`].
    #[inline]
    pub fn node(
        &mut self,
        label: Label,
        operands: &[GraphNode],
    ) -> Result<GraphNode, GraphError>
    {
        let node = self.reserve()?;
        self.define(node, label, operands)?;
        return Ok(node);
    }

    /// The graph of the builder's nodes, rooted at `root`. Each node keeps its
    /// position.
    ///
    /// # Specification
    /// - ensures: the graph holds each node of the builder at its position,
    ///   with its label and its operands, and its root at `root`.
    /// - fails: refuses a root or an operand that names no node, and a node
    ///   left undefined.
    /// - panics: none.
    /// - executable: none — the clause restates the copy.
    ///
    /// # Errors
    /// - [`GraphError::UnknownNode`]: the root or an operand names no node.
    /// - [`GraphError::Undefined`]: a node has no definition.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an undefined node and an operand past the last node
    ///   are each refused by name.
    /// - witness: `tests::minimal::the_builder_refuses_by_name`
    #[inline]
    pub fn finish(
        self,
        root: GraphNode,
    ) -> Result<PlanGraph, GraphError>
    {
        let count = self.nodes.len();
        if usize::from(root) >= count {
            return Err(GraphError::UnknownNode);
        }
        if self
            .operands
            .iter()
            .any(|&operand| usize::from(operand) >= count)
        {
            return Err(GraphError::UnknownNode);
        }
        let mut label_of = Vec::with_capacity(count);
        let mut starts = Vec::with_capacity(count.saturating_add(1));
        let mut operands = Vec::with_capacity(self.operands.len());
        for slot in &self.nodes {
            let &Some(slot) = slot
            else {
                return Err(GraphError::Undefined);
            };
            starts.push(u32::try_from(operands.len()).map_err(|_full| GraphError::TooManyNodes)?);
            let run = usize::try_from(slot.start)
                .ok()
                .zip(usize::try_from(slot.end).ok())
                .and_then(|(start, end)| self.operands.get(start .. end))
                .ok_or(GraphError::UnknownNode)?;
            operands.extend_from_slice(run);
            label_of.push(u32::from(slot.label));
        }
        starts.push(u32::try_from(operands.len()).map_err(|_full| GraphError::TooManyNodes)?);
        let graph = PlanGraph {
            labels: self.labels.held,
            label_of,
            starts,
            operands,
            root,
        };
        return Ok(graph.sorted());
    }
}

/// The place of a label among a graph's sorted labels: two labels compare as
/// their places do.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) struct LabelPlace(u32);

impl From<LabelPlace> for u32
{
    /// The place as a number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(place: LabelPlace) -> Self
    {
        return place.0;
    }
}

/// A plan, or a recursive system, as a graph: each node's label and its
/// operands in order, and the root.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PlanGraph
{
    /// The distinct labels that the nodes take, in their order.
    labels: Vec<Label>,
    /// The place in `labels` of each node's label.
    label_of: Vec<u32>,
    /// Where each node's operands start, and past the last node where they
    /// end.
    starts: Vec<u32>,
    /// The operands of every node, each node's in one run.
    operands: Vec<GraphNode>,
    /// The root.
    root: GraphNode,
}

impl PlanGraph
{
    /// The graph with its labels sorted, each label kept only when a node
    /// takes it.
    ///
    /// # Specification
    /// trivial.
    fn sorted(self) -> Self
    {
        let Self {
            labels,
            mut label_of,
            starts,
            operands,
            root,
        } = self;
        let mut used: Vec<bool> = alloc::vec![false; labels.len()];
        for &label in &label_of {
            if let Some(flag) = usize::try_from(label).ok().and_then(|at| used.get_mut(at)) {
                *flag = true;
            }
        }
        let mut place_of: Vec<u32> = alloc::vec![0; labels.len()];
        let mut order: Vec<(Label, u32)> = labels
            .into_iter()
            .zip(0_u32 ..)
            .zip(used)
            .filter_map(|(entry, kept)| kept.then_some(entry))
            .collect();
        order.sort_unstable();
        let mut sorted = Vec::with_capacity(order.len());
        for ((label, old), rank) in order.into_iter().zip(0_u32 ..) {
            if let Some(slot) = usize::try_from(old)
                .ok()
                .and_then(|at| place_of.get_mut(at))
            {
                *slot = rank;
            }
            sorted.push(label);
        }
        for label in &mut label_of {
            *label = usize::try_from(*label)
                .ok()
                .and_then(|at| place_of.get(at).copied())
                .unwrap_or_default();
        }
        return Self {
            labels: sorted,
            label_of,
            starts,
            operands,
            root,
        };
    }

    /// How many nodes the graph holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn node_count(&self) -> NodeCount
    {
        return NodeCount::from(self.label_of.len());
    }

    /// The root.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn root(&self) -> GraphNode
    {
        return self.root;
    }

    /// The operands of `node`, in order, or none for a node past the last.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn operands_of(
        &self,
        node: GraphNode,
    ) -> &[GraphNode]
    {
        let at = usize::from(node);
        let start = self.starts.get(at).copied();
        let end = self.starts.get(at.saturating_add(1)).copied();
        return start
            .zip(end)
            .and_then(|(start, end)| {
                let start = usize::try_from(start).ok()?;
                let end = usize::try_from(end).ok()?;
                return self.operands.get(start .. end);
            })
            .unwrap_or_default();
    }

    /// The place of `node`'s label among the graph's sorted labels, or none
    /// for a node past the last.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn label_place(
        &self,
        node: GraphNode,
    ) -> Option<LabelPlace>
    {
        return self
            .label_of
            .get(usize::from(node))
            .copied()
            .map(LabelPlace);
    }

    /// The label of `node`, or none for a node past the last.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn label_of(
        &self,
        node: GraphNode,
    ) -> Option<&Label>
    {
        let label = self.label_of.get(usize::from(node)).copied()?;
        return self.labels.get(usize::try_from(label).ok()?);
    }

    /// The recursive core: the nodes with operands that the matching leaves
    /// critical, and the faults that `theory-discrete-morse` finds in the
    /// matching.
    ///
    /// The rank of a leaf is zero, and the rank of a node is one more than the
    /// greatest rank of its operands. A node ranks when every path from it
    /// ends, so a node that reaches a cycle has no rank. The matching pairs
    /// each ranked node that has operands with the edge to its first operand
    /// one rank down. The work is linear in the nodes and the edges, and the
    /// check reads each cell once more.
    ///
    /// # Specification
    /// - ensures: the core holds exactly the nodes from which a path runs into
    ///   a cycle, in the order of their positions. The faults are zero, since
    ///   each gradient path runs down the ranks.
    /// - fails: a check whose walk passes its budget, which the count of the
    ///   nodes bounds, so it never fails.
    /// - panics: none.
    /// - executable: none — the clause restates the matching.
    ///
    /// # Errors
    /// - [`MorseError::PastBudget`]: the walk of the gradient reaches more
    ///   cells than the graph has nodes.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every generated plan has an empty core and no fault.
    ///   L3 — `x = 2^-x`, a node above it, and a two-cycle beside a leaf keep
    ///   their recursive nodes and no other.
    /// - witness: `tests::minimal::a_plan_has_an_empty_core`
    /// - witness: `tests::minimal::a_recursive_system_keeps_its_cycle_in_the_core`
    #[inline]
    pub fn core(&self) -> Result<Core, MorseError<Infallible>>
    {
        let mut gradient = Gradient::of(self);
        let mut cells: Vec<Cell> = (0_u32 ..)
            .take(self.label_of.len())
            .map(|node| Cell::Vertex(GraphNode(node)))
            .collect();
        cells.extend((0_u32 ..).take(self.operands.len()).map(Cell::Edge));
        let budget = Budget::from(self.label_of.len());
        let checked = collapse(&mut gradient, &cells, budget)?;
        let nodes = checked
            .critical()
            .iter()
            .filter_map(|cell| match *cell {
                Cell::Vertex(node) => (!self.operands_of(node).is_empty()).then_some(node),
                Cell::Edge(_) => None,
            })
            .collect();
        return Ok(Core {
            nodes,
            faults: checked.faults(),
        });
    }

    /// The minimal form of the part of the graph that the root reaches, and
    /// the key that its bytes give.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn minimal(&self) -> MinimalForm
    {
        return minimal(self);
    }
}

impl From<&Plan> for PlanGraph
{
    /// The graph of `plan`: each node at its position in the plan, its label
    /// its bytes without its children, and its operands its children in field
    /// order. The sum, the product, the meet and the join take their operands
    /// unordered.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(plan: &Plan) -> Self
    {
        let count = usize::from(plan.node_count());
        let mut labels = Labels::default();
        let mut label_of = Vec::with_capacity(count);
        let mut starts = Vec::with_capacity(count.saturating_add(1));
        let mut operands = Vec::with_capacity(count.saturating_mul(2));
        let mut entry = Entry::default();
        for (_, node) in plan.nodes() {
            starts.push(u32::try_from(operands.len()).unwrap_or(u32::MAX));
            operands.extend(node.edges().map(|edge| GraphNode::from(edge.node)));
            let order = match *node {
                Node::Real(Real::Add(..) | Real::Mul(..))
                | Node::Open(Open::Meet(..) | Open::Join(..)) => Operands::Unordered,
                Node::Real(_) | Node::Open(_) | Node::Domain(_) => Operands::Ordered,
            };
            entry.clear();
            if let Ok(skeleton) = node.clone().moved(|_child| Ok(NodeId::from(0_u32))) {
                entry.node(&skeleton);
            }
            let held = labels.find(LabelBytes(entry.as_ref()), order);
            let place = held.map_or_else(
                || {
                    return labels.insert(Label {
                        bytes: entry.as_ref().to_vec(),
                        operands: order,
                    });
                },
                Ok,
            );
            label_of.push(place.map_or(u32::MAX, u32::from));
        }
        starts.push(u32::try_from(operands.len()).unwrap_or(u32::MAX));
        let graph = Self {
            labels: labels.held,
            label_of,
            starts,
            operands,
            root: GraphNode::from(plan.root().node()),
        };
        return graph.sorted();
    }
}

/// The recursive core of a plan graph, and the faults that the check of its
/// matching finds.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Core
{
    /// The nodes with operands that the matching leaves critical.
    nodes: Vec<GraphNode>,
    /// What the check finds wrong with the matching.
    faults: Faults,
}

impl Core
{
    /// The nodes of the core, in the order of their positions.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn nodes(&self) -> &[GraphNode]
    {
        return &self.nodes;
    }

    /// What the check finds wrong with the matching: zero in each count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn faults(&self) -> Faults
    {
        return self.faults;
    }
}

/// A cell of a plan graph read as a complex: a node, or an operand edge by
/// its place among the graph's operands.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum Cell
{
    /// A node, of dimension zero.
    Vertex(GraphNode),
    /// An operand edge, of dimension one.
    Edge(u32),
}

/// The matching of a plan graph, read as Brown's collapsing scheme.
struct Gradient<'graph>
{
    /// The graph.
    graph: &'graph PlanGraph,
    /// The node that holds each edge.
    parents: Vec<GraphNode>,
    /// The edge that each node is matched with.
    partner: Vec<Option<u32>>,
    /// The node that each edge is matched with.
    matched: Vec<Option<GraphNode>>,
}

impl<'graph> Gradient<'graph>
{
    /// The matching of `graph`: each ranked node with operands matched with
    /// the edge to its first operand one rank down.
    ///
    /// # Specification
    /// trivial.
    fn of(graph: &'graph PlanGraph) -> Self
    {
        let count = graph.label_of.len();
        let edges = graph.operands.len();
        let mut parents = Vec::with_capacity(edges);
        for (node, pair) in (0_u32 ..).zip(graph.starts.windows(2)) {
            if let [start, end] = *pair {
                let run = usize::try_from(end.saturating_sub(start)).unwrap_or_default();
                parents.extend(core::iter::repeat_n(GraphNode(node), run));
            }
        }
        // The users of each node, by edge: the edges that name it.
        let mut fan: Vec<u32> = alloc::vec![0; count.saturating_add(1)];
        for &operand in &graph.operands {
            if let Some(slot) = fan.get_mut(usize::from(operand).saturating_add(1)) {
                *slot = slot.saturating_add(1);
            }
        }
        let mut running = 0_u32;
        for slot in &mut fan {
            running = running.saturating_add(*slot);
            *slot = running;
        }
        let mut cursor = fan.clone();
        let mut users: Vec<u32> = alloc::vec![0; edges];
        for (edge, &operand) in (0_u32 ..).zip(&graph.operands) {
            if let Some(next) = cursor.get_mut(usize::from(operand)) {
                if let Some(slot) = usize::try_from(*next).ok().and_then(|at| users.get_mut(at)) {
                    *slot = edge;
                }
                *next = next.saturating_add(1);
            }
        }
        // Kahn's order from the leaves up: a node ranks once every edge from
        // it reaches a ranked node.
        let mut waiting: Vec<u32> = graph
            .starts
            .windows(2)
            .map(|pair| {
                return match *pair {
                    [start, end] => end.saturating_sub(start),
                    _ => 0,
                };
            })
            .collect();
        let mut rank: Vec<Option<u32>> = alloc::vec![None; count];
        let mut height: Vec<u32> = alloc::vec![0; count];
        let mut ready: Vec<u32> = (0_u32 ..)
            .zip(&waiting)
            .filter_map(|(node, &left)| (left == 0).then_some(node))
            .collect();
        while let Some(node) = ready.pop() {
            let at = usize::try_from(node).unwrap_or(usize::MAX);
            let Some(&level) = height.get(at)
            else {
                continue;
            };
            if let Some(slot) = rank.get_mut(at) {
                *slot = Some(level);
            }
            let from = fan.get(at).copied().unwrap_or_default();
            let to = fan.get(at.saturating_add(1)).copied().unwrap_or_default();
            for &edge in usize::try_from(from)
                .ok()
                .zip(usize::try_from(to).ok())
                .and_then(|(from, to)| users.get(from .. to))
                .unwrap_or_default()
            {
                let Some(&parent) = usize::try_from(edge).ok().and_then(|at| parents.get(at))
                else {
                    continue;
                };
                let above = usize::from(parent);
                if let Some(slot) = height.get_mut(above) {
                    *slot = (*slot).max(level.saturating_add(1));
                }
                if let Some(left) = waiting.get_mut(above) {
                    *left = left.saturating_sub(1);
                    if *left == 0 {
                        ready.push(u32::from(parent));
                    }
                }
            }
        }
        let mut partner: Vec<Option<u32>> = alloc::vec![None; count];
        let mut matched: Vec<Option<GraphNode>> = alloc::vec![None; edges];
        for (node, slot) in (0_u32 ..).zip(&mut partner) {
            let at = usize::try_from(node).unwrap_or(usize::MAX);
            let Some(Some(level)) = rank.get(at).copied()
            else {
                continue;
            };
            let Some(below) = level.checked_sub(1)
            else {
                continue;
            };
            let start = graph.starts.get(at).copied().unwrap_or_default();
            let edge = graph
                .operands_of(GraphNode(node))
                .iter()
                .zip(start ..)
                .find(|&(&operand, _)| rank.get(usize::from(operand)).copied() == Some(Some(below)))
                .map(|(_, edge)| edge);
            if let Some(edge) = edge {
                *slot = Some(edge);
                if let Some(back) = usize::try_from(edge)
                    .ok()
                    .and_then(|at| matched.get_mut(at))
                {
                    *back = Some(GraphNode(node));
                }
            }
        }
        return Self {
            graph,
            parents,
            partner,
            matched,
        };
    }
}

impl Complex for Gradient<'_>
{
    type Cell = Cell;
    type Fault = Infallible;

    /// Whether `cell` is a node or an edge of the graph.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn standing(
        &mut self,
        cell: &Cell,
    ) -> Result<Standing, Infallible>
    {
        let inside = match *cell {
            Cell::Vertex(node) => usize::from(node) < self.graph.label_of.len(),
            Cell::Edge(edge) => {
                usize::try_from(edge).is_ok_and(|at| at < self.graph.operands.len())
            },
        };
        return Ok(if inside {
            Standing::Inside
        }
        else {
            Standing::Outside
        });
    }

    /// The faces of an edge: its node with the incidence minus one, and its
    /// operand with the incidence one. A loop's one face has the incidence
    /// zero, and a node has no face.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn faces(
        &mut self,
        cell: &Cell,
        faces: &mut Vec<(Cell, Incidence)>,
    ) -> Result<(), Infallible>
    {
        let Cell::Edge(edge) = *cell
        else {
            return Ok(());
        };
        let at = usize::try_from(edge).unwrap_or(usize::MAX);
        let (Some(&parent), Some(&operand)) = (self.parents.get(at), self.graph.operands.get(at))
        else {
            return Ok(());
        };
        if parent == operand {
            faces.push((Cell::Vertex(parent), Incidence::from(0_i64)));
        }
        else {
            faces.push((Cell::Vertex(parent), Incidence::from(-1_i64)));
            faces.push((Cell::Vertex(operand), Incidence::from(1_i64)));
        }
        return Ok(());
    }
}

impl Scheme for Gradient<'_>
{
    /// A matched node is redundant with its edge, a matched edge collapsible
    /// with its node, and every other cell critical.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn class(
        &mut self,
        cell: &Cell,
    ) -> Result<Class<Cell>, Infallible>
    {
        let class = match *cell {
            Cell::Vertex(node) => self
                .partner
                .get(usize::from(node))
                .copied()
                .flatten()
                .map_or(Class::Critical, |edge| Class::Redundant(Cell::Edge(edge))),
            Cell::Edge(edge) => usize::try_from(edge)
                .ok()
                .and_then(|at| self.matched.get(at).copied().flatten())
                .map_or(Class::Critical, |node| {
                    Class::Collapsible(Cell::Vertex(node))
                }),
        };
        return Ok(class);
    }
}
