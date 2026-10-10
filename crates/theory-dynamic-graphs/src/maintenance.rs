//! Incremental **acyclicity maintenance**: a topological order of a directed
//! graph kept current under edge insertion.
//!
//! [`AcyclicityMaintenance`] holds every admitted node in a
//! [`OrderMaintenance`] whose list order *is* the topological order, so
//! comparing two existing nodes uses their order labels. An insertion the
//! standing order already witnesses needs no search or relocation; recording it
//! still scans the source row for a duplicate. An insertion
//! that runs against the order is repaired by a bounded two-way search around
//! the offending pair, which either finds the cycle the insertion would close
//! or relocates exactly the nodes whose relative order the insertion changed.
//!
//! # The search is bounded by the order, not by the graph
//!
//! When `source` already sits after `target`, only nodes lying between them in
//! the standing order can have their relative order changed by the new edge.
//! The forward search from `target` therefore follows successors only while
//! they precede `source`, and the backward search from `source` follows
//! predecessors only while they follow `target`. Everything outside that window
//! keeps its position, and the repair touches nothing outside the two searched
//! sets — which is what makes the cost a function of the affected region rather
//! than of the graph.
//!
//! # The relocation preserves the slots it found
//!
//! The two searched sets are relocated into **exactly the order positions they
//! already occupied**, with the backward set's members first and the forward
//! set's after them. Nodes interleaved between those positions that belong to
//! neither set are not moved and keep their neighbours, which is what keeps
//! their relation to the relocated nodes correct without inspecting them.

use alloc::vec::Vec;
use core::cmp::Ordering;

use anodized::spec;
use gandr_theory_graphs::CycleWitness;
use gandr_theory_graphs::EdgeId;
use gandr_theory_graphs::EdgeSource;
use gandr_theory_graphs::NodeCount;
use gandr_theory_graphs::NodeId;
use gandr_theory_orders::OrderError;
use gandr_theory_orders::OrderMaintenance;
use gandr_theory_orders::Pos;

use crate::slot::SlotIndex;

/// The number of edges an [`AcyclicityMaintenance`] currently holds.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct AdmittedEdgeCount(u64);

impl AdmittedEdgeCount
{
    /// This count raised by one, saturating at the representable maximum.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn saturating_increment(self) -> Self
    {
        return Self(self.0.saturating_add(1));
    }
}

impl From<AdmittedEdgeCount> for u64
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: AdmittedEdgeCount) -> Self
    {
        return value.0;
    }
}

/// The number of edge insertions offered to an [`AcyclicityMaintenance`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct InsertionCount(u64);

impl InsertionCount
{
    /// This count raised by one, saturating at the representable maximum.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn saturating_increment(self) -> Self
    {
        return Self(self.0.saturating_add(1));
    }
}

impl From<InsertionCount> for u64
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: InsertionCount) -> Self
    {
        return value.0;
    }
}

/// The number of insertions that ran against the standing order and were
/// repaired.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RepairCount(u64);

impl RepairCount
{
    /// This count raised by one, saturating at the representable maximum.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn saturating_increment(self) -> Self
    {
        return Self(self.0.saturating_add(1));
    }
}

impl From<RepairCount> for u64
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: RepairCount) -> Self
    {
        return value.0;
    }
}

/// The number of insertions refused because they would close a cycle.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RefusalCount(u64);

impl RefusalCount
{
    /// This count raised by one, saturating at the representable maximum.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn saturating_increment(self) -> Self
    {
        return Self(self.0.saturating_add(1));
    }
}

impl From<RefusalCount> for u64
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: RefusalCount) -> Self
    {
        return value.0;
    }
}

/// The number of nodes the bounded searches have reached, across every
/// insertion.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct VisitCount(u64);

impl VisitCount
{
    /// This count raised by one, saturating at the representable maximum.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn saturating_increment(self) -> Self
    {
        return Self(self.0.saturating_add(1));
    }
}

impl From<VisitCount> for u64
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: VisitCount) -> Self
    {
        return value.0;
    }
}

/// The number of nodes moved within the maintained order, across every
/// insertion.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RelocationCount(u64);

impl RelocationCount
{
    /// This count raised by one, saturating at the representable maximum.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn saturating_increment(self) -> Self
    {
        return Self(self.0.saturating_add(1));
    }
}

impl From<RelocationCount> for u64
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: RelocationCount) -> Self
    {
        return value.0;
    }
}

/// Whether the maintained order is a topological order of the admitted edges.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct TopologicalOrderStatus(bool);

impl From<TopologicalOrderStatus> for bool
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: TopologicalOrderStatus) -> Self
    {
        return value.0;
    }
}

impl core::ops::Not for TopologicalOrderStatus
{
    type Output = Self;

    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn not(self) -> Self::Output
    {
        return Self(!self.0);
    }
}

/// A search epoch, stamped into the reusable mark buffers so a bounded search
/// clears its state in constant time instead of rewriting the buffers.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Epoch(u64);

impl Epoch
{
    /// The epoch no search ever runs under, so a freshly grown buffer entry is
    /// unmarked for every real search.
    const UNVISITED: Self = Self(0);

    /// This epoch advanced by one, saturating at the representable maximum.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn saturating_increment(self) -> Self
    {
        return Self(self.0.saturating_add(1));
    }
}

/// A failure of an [`AcyclicityMaintenance`] operation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MaintenanceError
{
    /// The maintained order could not admit or relocate an element.
    Order(OrderError),
    /// A node identifier does not address a slot of this structure.
    NodeCapacity,
    /// A handle the structure still tracks no longer resolves in the
    /// maintained order.
    OrderDesynchronized,
    /// An internal checked arithmetic operation overflowed.
    ArithmeticOverflow,
}

/// The verdict on one offered edge.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EdgeVerdict
{
    /// The standing order already places the source before the target, so the
    /// edge was recorded without touching the order.
    Admitted,
    /// The edge ran against the standing order and was recorded after
    /// relocating the affected region.
    AdmittedAfterRepair,
    /// The edge would close a cycle and was **not** recorded; the witness is
    /// the closed walk it would have closed.
    Refused(CycleWitness),
}

/// The work an [`AcyclicityMaintenance`] has performed since construction.
///
/// Visits and relocations expose the affected-region work. They exclude
/// adjacency scans, sorting, allocation, and order-label maintenance, so they
/// are operation projections rather than elapsed time or total complexity.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct MaintenanceTelemetry
{
    /// Edges offered to [`AcyclicityMaintenance::insert_edge`].
    pub insertions: InsertionCount,
    /// Offered edges that ran against the standing order and were repaired.
    pub repairs: RepairCount,
    /// Offered edges refused as cycle-closing.
    pub refusals: RefusalCount,
    /// Nodes reached by the bounded searches.
    pub nodes_visited: VisitCount,
    /// Nodes moved within the maintained order.
    pub nodes_relocated: RelocationCount,
}

/// Reusable marks, searches, and relocation workspace.
/// Capacity grows with the largest node domain and affected region seen.
#[derive(Debug, Default)]
struct Scratch
{
    /// The epoch at which each node was last reached by a forward search.
    forward_mark: Vec<Epoch>,
    /// The epoch at which each node was last reached by a backward search.
    backward_mark: Vec<Epoch>,
    /// The forward search's predecessor of each node, meaningful exactly where
    /// [`Scratch::forward_mark`] carries the current epoch.
    forward_parent: Vec<NodeId>,
    /// The epoch of the search most recently begun.
    epoch: Epoch,
    /// The explicit depth-first work stack; recursion is never used, so the
    /// search depth is bounded by the heap rather than the native stack.
    stack: Vec<NodeId>,
    /// Descendants reached by the forward search.
    forward_region: Vec<NodeId>,
    /// Ancestors reached by the backward search.
    backward_region: Vec<NodeId>,
    /// Backward region paired with its old positions, in standing order.
    backward_sorted: Vec<(NodeId, Pos)>,
    /// Forward region paired with its old positions, in standing order.
    forward_sorted: Vec<(NodeId, Pos)>,
    /// All affected slots in standing order.
    slots: Vec<(NodeId, Pos)>,
    /// The backward-then-forward node arrangement.
    arrangement: Vec<NodeId>,
    /// Nearest unaffected predecessor for each affected slot.
    anchors: Vec<Option<Pos>>,
}

/// Outcome of the forward half of a bounded repair.
enum ForwardDiscovery
{
    /// Nodes reached without closing the offered edge.
    Reached,
    /// Closed walk through the offered edge.
    Cycle(CycleWitness),
}

/// What the bounded two-way search around a violating insertion found.
enum Discovery
{
    /// The insertion closes a cycle; the witness is that closed walk.
    Cycle(CycleWitness),
    /// The affected region has been relocated to admit the insertion.
    Repaired,
}

/// A directed graph whose **topological order is maintained under edge
/// insertion**, refusing exactly the edges that would close a cycle.
///
/// Nodes are dense [`NodeId`]s and are created on demand: an insertion naming a
/// node the structure has not seen appends it to the end of the order, which is
/// always topologically valid because a fresh node has no edges.
pub struct AcyclicityMaintenance
{
    /// The maintained topological order; each element's payload is the node it
    /// orders, and list order is topological order.
    order: OrderMaintenance<NodeId>,
    /// Each node's handle into [`AcyclicityMaintenance::order`], indexed by
    /// dense node id.
    positions: Vec<Pos>,
    /// Admitted outgoing edges per node, indexed by dense node id.
    successors: Vec<Vec<NodeId>>,
    /// Admitted incoming edges per node, indexed by dense node id.
    predecessors: Vec<Vec<NodeId>>,
    /// The number of admitted edges.
    edges: AdmittedEdgeCount,
    /// The work counters.
    telemetry: MaintenanceTelemetry,
    /// The reusable search buffers.
    scratch: Scratch,
}

impl AcyclicityMaintenance
{
    /// An empty structure with no nodes and no edges.
    ///
    /// # Specification
    /// - ensures: a structure whose node count and admitted-edge count are both
    ///   zero.
    /// - fails: propagates [`OrderError::StructureIdExhausted`] as
    ///   [`MaintenanceError::Order`] when the process has no distinct
    ///   order-structure identity left.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`MaintenanceError::Order`] when the underlying order structure
    /// cannot be constructed.
    ///
    /// # Adequacy
    /// - hypothesis: L2 differential streams and L3 boundaries distinguish
    ///   wrong verdicts, lost edges and invalid maintained state on finite
    ///   graphs.
    /// - witness: `maintenance::tests::the_maintained_order_is_topological`
    #[inline]
    #[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|graph| u32::from(graph.nodes()) == 0 && u64::from(graph.admitted_edges()) == 0))]
    pub fn new() -> Result<Self, MaintenanceError>
    {
        let order = OrderMaintenance::new()?;
        return Ok(Self {
            order,
            positions: Vec::new(),
            successors: Vec::new(),
            predecessors: Vec::new(),
            edges: AdmittedEdgeCount::default(),
            telemetry: MaintenanceTelemetry::default(),
            scratch: Scratch::default(),
        });
    }

    /// An edgeless structure already holding `count` nodes, in dense id order.
    ///
    /// # Specification
    /// - ensures: nodes `0 .. count` exist and stand in ascending dense-id
    ///   order, which is topologically valid because no edge exists yet.
    /// - fails: [`MaintenanceError::Order`] when the order structure cannot be
    ///   constructed or cannot admit that many elements;
    ///   [`MaintenanceError::ArithmeticOverflow`] when the count does not fit
    ///   the host address space.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns [`MaintenanceError::Order`] or
    /// [`MaintenanceError::ArithmeticOverflow`] as above.
    ///
    /// # Adequacy
    /// - hypothesis: L2 differential streams and L3 boundaries distinguish
    ///   wrong verdicts, lost edges and invalid maintained state on finite
    ///   graphs.
    /// - witness: `maintenance::tests::the_maintained_order_is_topological`
    #[inline]
    #[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|graph| graph.nodes() == count && u64::from(graph.admitted_edges()) == 0))]
    pub fn with_nodes(count: NodeCount) -> Result<Self, MaintenanceError>
    {
        let mut structure = Self::new()?;
        let total = usize::try_from(u32::from(count))
            .map_err(|_ignored| MaintenanceError::ArithmeticOverflow)?;
        if let Some(last) = total.checked_sub(1) {
            let raw =
                u32::try_from(last).map_err(|_ignored| MaintenanceError::ArithmeticOverflow)?;
            structure.ensure_node(NodeId::from(raw))?;
        }
        return Ok(structure);
    }

    /// The number of nodes the structure holds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn nodes(&self) -> NodeCount
    {
        return NodeCount::from(u32::try_from(self.positions.len()).unwrap_or(u32::MAX));
    }

    /// The number of admitted edges.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn admitted_edges(&self) -> AdmittedEdgeCount
    {
        return self.edges;
    }

    /// The work performed since construction.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn telemetry(&self) -> MaintenanceTelemetry
    {
        return self.telemetry;
    }

    /// The relative position of two nodes in the maintained order.
    ///
    /// # Specification
    /// - ensures: `Ok(Less)` exactly when `left` precedes `right`, and
    ///   `Ok(Equal)` exactly when the two identifiers are the same node.
    /// - fails: `NodeCapacity` for an unknown node; `OrderDesynchronized` for a
    ///   stale position.
    /// - panics: none.
    ///
    /// # Errors
    /// Returns the typed node-capacity, arithmetic or maintained-state failure.
    ///
    /// # Adequacy
    /// - hypothesis: L2 differential streams and L3 boundaries distinguish
    ///   wrong verdicts, lost edges and invalid maintained state on finite
    ///   graphs.
    /// - witness: `maintenance::tests::the_maintained_order_is_topological`
    #[inline]
    #[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|comparison| (*comparison == Ordering::Equal) == (left == right)))]
    pub fn compare(
        &self,
        left: NodeId,
        right: NodeId,
    ) -> Result<Ordering, MaintenanceError>
    {
        let left_position = self.position(left)?;
        let right_position = self.position(right)?;
        self.order
            .cmp(left_position, right_position)
            .ok_or(MaintenanceError::OrderDesynchronized)
    }

    /// The nodes in maintained order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn nodes_in_order(&self) -> impl Iterator<Item = NodeId> + '_
    {
        return self.order.iter().map(|(_position, &node)| node);
    }

    /// Whether every admitted edge runs forward in the maintained order.
    ///
    /// This is the structure's own invariant, stated as a query so a consumer —
    /// or a differential — can check it rather than trust it.
    ///
    /// # Specification
    /// - ensures: positive exactly when every admitted edge `source -> target`
    ///   has `source` strictly preceding `target` in the maintained order.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 boundary — a hand-relabelled order in which one
    ///   admitted edge runs backwards is distinguished from the same graph
    ///   before the relabelling, which is what makes this query the
    ///   differential's teeth rather than a restatement of the insertion path.
    /// - witness: `maintenance::tests::a_corrupted_order_is_caught_by_the_invariant`
    /// - witness: `maintenance::tests::the_maintained_order_is_topological`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.0 == self.successors.iter().enumerate().all(|(source, row)| u32::try_from(source).is_ok_and(|source| row.iter().all(|&target| self.compare(NodeId::from(source), target) == Ok(Ordering::Less)))))]
    pub fn order_is_topological(&self) -> TopologicalOrderStatus
    {
        for (index, row) in self.successors.iter().enumerate() {
            let Ok(raw) = u32::try_from(index)
            else {
                return TopologicalOrderStatus(false);
            };
            let source = NodeId::from(raw);
            for &target in row {
                if self.compare(source, target) != Ok(Ordering::Less) {
                    return TopologicalOrderStatus(false);
                }
            }
        }
        return TopologicalOrderStatus(true);
    }

    /// **Offer one directed edge**, admitting it exactly when the resulting
    /// graph stays acyclic.
    ///
    /// The standing order decides the cheap case on its own: when it already
    /// places the source before the target the edge is recorded and nothing
    /// moves. Otherwise a bounded two-way search around the pair either returns
    /// the cycle the edge would close — in which case the edge is **not**
    /// recorded — or identifies the region whose relative order the edge
    /// changes, which is relocated before the edge is recorded.
    ///
    /// A repeated edge is admitted without being recorded twice, and a self
    /// loop is refused with the one-node closed walk as its witness.
    ///
    /// # Specification
    /// - requires: nothing; unseen nodes are created at the end of the order.
    /// - ensures: [`EdgeVerdict::Refused`] exactly when the offered edge closes
    ///   a cycle over the admitted edges, in which case the structure is
    ///   unchanged apart from any nodes the offer created; otherwise the edge
    ///   is admitted and the maintained order stays topological.
    /// - provides: a [`CycleWitness`] on refusal whose walk is closed and whose
    ///   edges are the offered edge together with admitted edges.
    /// - fails: [`MaintenanceError::Order`] when the order cannot admit or
    ///   relocate an element, [`MaintenanceError::OrderDesynchronized`] when a
    ///   tracked handle no longer resolves, and
    ///   [`MaintenanceError::ArithmeticOverflow`] on an internal conversion the
    ///   node capacity precludes.
    /// - panics: none.
    /// - intension: the work is bounded by the region between the two endpoints
    ///   in the standing order — the searches never leave it, and no node
    ///   outside the two searched sets is moved.
    ///
    /// # Errors
    /// Returns [`MaintenanceError`] as enumerated above.
    ///
    /// # Adequacy
    /// - hypothesis: L1 evidence + property — over generated edge streams every
    ///   verdict agrees with a batch cycle check run over the admitted edges
    ///   plus the offered one, and the maintained order stays topological after
    ///   every admission. Boundary: the same edge is `Admitted` when the order
    ///   already witnesses it and `AdmittedAfterRepair` when it does not, and a
    ///   self loop is `Refused` where a parallel edge is not.
    /// - witness: `maintenance::tests::an_edge_the_order_witnesses_is_admitted_without_moving_anything`
    /// - witness: `maintenance::tests::a_violating_edge_is_repaired_locally`
    /// - witness: `maintenance::tests::a_cycle_closing_edge_is_refused_with_its_walk`
    /// - witness: `maintenance::tests::a_self_loop_is_refused`
    /// - witness: `dynamic_graphs::differential::tests::incremental_verdicts_equal_the_batch_answer`
    #[inline]
    #[spec(ensures: |ret| ret.is_err() || bool::from(self.order_is_topological()))]
    pub fn insert_edge(
        &mut self,
        edge: EdgeId,
    ) -> Result<EdgeVerdict, MaintenanceError>
    {
        self.telemetry.insertions = self.telemetry.insertions.saturating_increment();
        self.ensure_node(edge.source)?;
        self.ensure_node(edge.target)?;
        if edge.source == edge.target {
            self.telemetry.refusals = self.telemetry.refusals.saturating_increment();
            return Ok(EdgeVerdict::Refused(CycleWitness {
                nodes: alloc::vec![edge.source, edge.source],
                edges: alloc::vec![edge],
            }));
        }
        let source_position = self.position(edge.source)?;
        let target_position = self.position(edge.target)?;
        let standing = self
            .order
            .cmp(source_position, target_position)
            .ok_or(MaintenanceError::OrderDesynchronized)?;
        if standing == Ordering::Less {
            self.record_edge(edge)?;
            return Ok(EdgeVerdict::Admitted);
        }
        let discovery = self.repair(edge)?;
        match discovery {
            | Discovery::Cycle(witness) => {
                self.telemetry.refusals = self.telemetry.refusals.saturating_increment();
                Ok(EdgeVerdict::Refused(witness))
            },
            | Discovery::Repaired => {
                self.record_edge(edge)?;
                self.telemetry.repairs = self.telemetry.repairs.saturating_increment();
                Ok(EdgeVerdict::AdmittedAfterRepair)
            },
        }
    }

    // ----- internal helpers ------------------------------------------------

    /// The dense vector index addressed by `node`.
    ///
    /// # Errors
    /// Returns [`MaintenanceError::ArithmeticOverflow`] when the identifier
    /// does not fit the host address space.
    ///
    /// # Specification
    /// - ensures: Converts a node identity to its checked host slot.
    /// - fails: returns `ArithmeticOverflow` if the identifier cannot fit the
    ///   host.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 differential streams and L3 boundaries distinguish
    ///   wrong verdicts, lost edges and invalid maintained state on finite
    ///   graphs.
    /// - witness: `maintenance::tests::the_maintained_order_is_topological`
    #[inline]
    #[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|index| usize::try_from(u32::from(node)) == Ok(usize::from(*index))))]
    fn index_of(node: NodeId) -> Result<SlotIndex, MaintenanceError>
    {
        return SlotIndex::try_from(node).map_err(|_ignored| MaintenanceError::ArithmeticOverflow);
    }

    /// The order handle of `node`.
    ///
    /// # Errors
    /// Returns [`MaintenanceError::NodeCapacity`] when the identifier addresses
    /// no maintained node.
    ///
    /// # Specification
    /// - ensures: Returns the maintained handle for the requested node.
    /// - fails: returns `NodeCapacity` for an unknown node or
    ///   `ArithmeticOverflow` for its index.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 differential streams and L3 boundaries distinguish
    ///   wrong verdicts, lost edges and invalid maintained state on finite
    ///   graphs.
    /// - witness: `maintenance::tests::the_maintained_order_is_topological`
    #[inline]
    #[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|position| self.order.get(*position) == Some(&node)))]
    fn position(
        &self,
        node: NodeId,
    ) -> Result<Pos, MaintenanceError>
    {
        let index = Self::index_of(node)?;
        return self
            .positions
            .get(usize::from(index))
            .copied()
            .ok_or(MaintenanceError::NodeCapacity);
    }

    /// Creates every node up to and including `node`, appending each to the end
    /// of the order.
    ///
    /// Appending is topologically valid because a node created here has no
    /// edges yet.
    ///
    /// # Errors
    /// Returns [`MaintenanceError::Order`] when the order cannot admit an
    /// element, or [`MaintenanceError::ArithmeticOverflow`] on an internal
    /// conversion.
    ///
    /// # Specification
    /// - ensures: Appends all missing dense nodes, preserving existing edges
    ///   and order.
    /// - fails: returns `NodeCapacity` for an unrepresentable node count, or an
    ///   order/index error.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 differential streams and L3 boundaries distinguish
    ///   wrong verdicts, lost edges and invalid maintained state on finite
    ///   graphs.
    /// - witness: `maintenance::tests::the_maintained_order_is_topological`
    #[inline]
    #[spec(ensures: |ret| ret.is_err() || u32::from(self.nodes()) > u32::from(node))]
    fn ensure_node(
        &mut self,
        node: NodeId,
    ) -> Result<(), MaintenanceError>
    {
        if u32::from(node) == u32::MAX {
            return Err(MaintenanceError::NodeCapacity);
        }
        let index = Self::index_of(node)?;
        let required = usize::from(index)
            .checked_add(1)
            .ok_or(MaintenanceError::ArithmeticOverflow)?;
        while self.positions.len() < required {
            let raw = u32::try_from(self.positions.len())
                .map_err(|_ignored| MaintenanceError::ArithmeticOverflow)?;
            let fresh = NodeId::from(raw);
            let position = self.order.push_back(fresh)?;
            self.positions.push(position);
            self.successors.push(Vec::new());
            self.predecessors.push(Vec::new());
        }
        return Ok(());
    }

    /// Records `edge` in both adjacency directions, ignoring a repeat.
    ///
    /// # Errors
    /// Returns [`MaintenanceError::NodeCapacity`] when either endpoint
    /// addresses no maintained node, or
    /// [`MaintenanceError::ArithmeticOverflow`] on an internal conversion.
    ///
    /// # Specification
    /// - ensures: Records the edge in both adjacency directions without
    ///   duplicating it.
    /// - fails: returns `NodeCapacity` for an absent endpoint or
    ///   `ArithmeticOverflow` for its index.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 differential streams and L3 boundaries distinguish
    ///   wrong verdicts, lost edges and invalid maintained state on finite
    ///   graphs.
    /// - witness: `maintenance::tests::the_maintained_order_is_topological`
    #[inline]
    #[spec(ensures: |ret| ret.is_err() || self.successors(edge.source).any(|node| node == edge.target))]
    fn record_edge(
        &mut self,
        edge: EdgeId,
    ) -> Result<(), MaintenanceError>
    {
        let source_index = Self::index_of(edge.source)?;
        let target_index = Self::index_of(edge.target)?;
        let outgoing = self
            .successors
            .get_mut(usize::from(source_index))
            .ok_or(MaintenanceError::NodeCapacity)?;
        if outgoing.contains(&edge.target) {
            return Ok(());
        }
        outgoing.push(edge.target);
        let incoming = self
            .predecessors
            .get_mut(usize::from(target_index))
            .ok_or(MaintenanceError::NodeCapacity)?;
        incoming.push(edge.source);
        self.edges = self.edges.saturating_increment();
        return Ok(());
    }

    /// Repairs a violating insertion or returns its closing cycle.
    ///
    /// The scratch buffers are taken out for the duration so the search can
    /// call the ordinary shared-reference helpers, and are restored on
    /// every path.
    ///
    /// # Errors
    /// Returns [`MaintenanceError`] as [`AcyclicityMaintenance::insert_edge`]
    /// enumerates.
    ///
    /// # Specification
    /// - ensures: Leaves adjacency unchanged and either returns a closing cycle
    ///   or relocates the affected sets into an admitting order.
    /// - fails: propagates checked node, order-handle, and arithmetic failures.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 differential streams and L3 boundaries distinguish
    ///   wrong verdicts, lost edges and invalid maintained state on finite
    ///   graphs.
    /// - witness: `maintenance::tests::the_maintained_order_is_topological`
    #[inline]
    #[spec(ensures: |ret| ret.is_err() || bool::from(self.order_is_topological()))]
    fn repair(
        &mut self,
        edge: EdgeId,
    ) -> Result<Discovery, MaintenanceError>
    {
        let mut scratch = core::mem::take(&mut self.scratch);
        let outcome = self.search(&mut scratch, edge);
        self.scratch = scratch;
        return outcome;
    }

    /// Searches and relocates the affected sets through reusable scratch state.
    ///
    /// # Errors
    /// Returns [`MaintenanceError`] as [`AcyclicityMaintenance::insert_edge`]
    /// enumerates.
    ///
    /// # Specification
    /// - ensures: Refuses a closing cycle without moving nodes, or relocates
    ///   the affected sets while preserving admitted-edge topology.
    /// - fails: propagates checked node, order-handle, and arithmetic failures.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 differential streams and L3 boundaries distinguish
    ///   wrong verdicts, lost edges and invalid maintained state on finite
    ///   graphs.
    /// - witness: `maintenance::tests::the_maintained_order_is_topological`
    #[inline]
    #[spec(ensures: |ret| ret.is_err() || bool::from(self.order_is_topological()))]
    fn search(
        &mut self,
        scratch: &mut Scratch,
        edge: EdgeId,
    ) -> Result<Discovery, MaintenanceError>
    {
        let width = self.positions.len();
        scratch.forward_mark.resize(width, Epoch::UNVISITED);
        scratch.backward_mark.resize(width, Epoch::UNVISITED);
        scratch.forward_parent.resize(width, NodeId::default());
        if scratch.epoch.0 == u64::MAX {
            scratch.forward_mark.fill(Epoch::UNVISITED);
            scratch.backward_mark.fill(Epoch::UNVISITED);
            scratch.epoch = Epoch::UNVISITED;
        }
        scratch.epoch = scratch.epoch.saturating_increment();
        let epoch = scratch.epoch;

        match self.search_forward(scratch, edge, epoch)? {
            | ForwardDiscovery::Reached => {},
            | ForwardDiscovery::Cycle(witness) => return Ok(Discovery::Cycle(witness)),
        }
        self.search_backward(scratch, edge, epoch)?;
        self.relocate(scratch)?;
        return Ok(Discovery::Repaired);
    }

    /// The forward search: descendants of the edge's target that precede the
    /// edge's source in the standing order.
    ///
    /// Returns `ForwardDiscovery::Cycle` when the search reaches the
    /// edge's source, which is exactly the cycle the insertion would close.
    ///
    /// # Errors
    /// Returns [`MaintenanceError`] as [`AcyclicityMaintenance::insert_edge`]
    /// enumerates.
    ///
    /// # Specification
    /// - ensures: Finds descendants before the source, or a closed walk through
    ///   the offered edge.
    /// - fails: propagates checked node, order-handle, and arithmetic failures.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 differential streams and L3 boundaries distinguish
    ///   wrong verdicts, lost edges and invalid maintained state on finite
    ///   graphs.
    /// - witness: `maintenance::tests::the_maintained_order_is_topological`
    #[inline]
    #[spec(ensures: |ret| ret.is_err() || bool::from(self.order_is_topological()))]
    fn search_forward(
        &mut self,
        scratch: &mut Scratch,
        edge: EdgeId,
        epoch: Epoch,
    ) -> Result<ForwardDiscovery, MaintenanceError>
    {
        scratch.forward_region.clear();
        scratch.stack.clear();
        let target_index = Self::index_of(edge.target)?;
        let mark = scratch
            .forward_mark
            .get_mut(usize::from(target_index))
            .ok_or(MaintenanceError::NodeCapacity)?;
        *mark = epoch;
        scratch.stack.push(edge.target);
        while let Some(node) = scratch.stack.pop() {
            scratch.forward_region.push(node);
            self.telemetry.nodes_visited = self.telemetry.nodes_visited.saturating_increment();
            let node_index = Self::index_of(node)?;
            let row = self
                .successors
                .get(usize::from(node_index))
                .ok_or(MaintenanceError::NodeCapacity)?;
            for &successor in row {
                if successor == edge.source {
                    let witness = Self::cycle_from(scratch, edge, node)?;
                    return Ok(ForwardDiscovery::Cycle(witness));
                }
                if self.compare(successor, edge.source) != Ok(Ordering::Less) {
                    continue;
                }
                let successor_index = Self::index_of(successor)?;
                let successor_mark = scratch
                    .forward_mark
                    .get_mut(usize::from(successor_index))
                    .ok_or(MaintenanceError::NodeCapacity)?;
                if *successor_mark == epoch {
                    continue;
                }
                *successor_mark = epoch;
                let parent = scratch
                    .forward_parent
                    .get_mut(usize::from(successor_index))
                    .ok_or(MaintenanceError::NodeCapacity)?;
                *parent = node;
                scratch.stack.push(successor);
            }
        }
        return Ok(ForwardDiscovery::Reached);
    }

    /// The backward search: ancestors of the edge's source that follow the
    /// edge's target in the standing order.
    ///
    /// # Errors
    /// Returns [`MaintenanceError`] as [`AcyclicityMaintenance::insert_edge`]
    /// enumerates.
    ///
    /// # Specification
    /// - ensures: Finds source ancestors lying after the target.
    /// - fails: propagates checked node, order-handle, and arithmetic failures.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 differential streams and L3 boundaries distinguish
    ///   wrong verdicts, lost edges and invalid maintained state on finite
    ///   graphs.
    /// - witness: `maintenance::tests::the_maintained_order_is_topological`
    #[inline]
    #[spec(ensures: |ret| ret.is_err() || scratch.backward_region.iter().all(|&node| self.compare(node, edge.target) == Ok(Ordering::Greater)))]
    fn search_backward(
        &mut self,
        scratch: &mut Scratch,
        edge: EdgeId,
        epoch: Epoch,
    ) -> Result<(), MaintenanceError>
    {
        scratch.backward_region.clear();
        scratch.stack.clear();
        let source_index = Self::index_of(edge.source)?;
        let mark = scratch
            .backward_mark
            .get_mut(usize::from(source_index))
            .ok_or(MaintenanceError::NodeCapacity)?;
        *mark = epoch;
        scratch.stack.push(edge.source);
        while let Some(node) = scratch.stack.pop() {
            scratch.backward_region.push(node);
            self.telemetry.nodes_visited = self.telemetry.nodes_visited.saturating_increment();
            let node_index = Self::index_of(node)?;
            let row = self
                .predecessors
                .get(usize::from(node_index))
                .ok_or(MaintenanceError::NodeCapacity)?;
            for &predecessor in row {
                if self.compare(predecessor, edge.target) != Ok(Ordering::Greater) {
                    continue;
                }
                let predecessor_index = Self::index_of(predecessor)?;
                let predecessor_mark = scratch
                    .backward_mark
                    .get_mut(usize::from(predecessor_index))
                    .ok_or(MaintenanceError::NodeCapacity)?;
                if *predecessor_mark == epoch {
                    continue;
                }
                *predecessor_mark = epoch;
                scratch.stack.push(predecessor);
            }
        }
        return Ok(());
    }

    /// Rebuilds the closed walk the offered edge would close, from the forward
    /// search's parent links.
    ///
    /// `last` is the node whose successor is the edge's source, so the walk
    /// runs from the edge's target down the parent chain to `last`, on to
    /// the edge's source, and back to the target along the offered edge.
    ///
    /// # Errors
    /// Returns [`MaintenanceError::OrderDesynchronized`] when the parent chain
    /// does not reach the edge's target within the node count, which the
    /// search's own construction precludes.
    ///
    /// # Specification
    /// - ensures: Reconstructs the closed walk containing the offered edge.
    /// - fails: returns `OrderDesynchronized` for a broken parent chain, or a
    ///   node/index error.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 differential streams and L3 boundaries distinguish
    ///   wrong verdicts, lost edges and invalid maintained state on finite
    ///   graphs.
    /// - witness: `maintenance::tests::the_maintained_order_is_topological`
    #[inline]
    #[spec(ensures: |ret| ret.is_err() || ret.as_ref().is_ok_and(|cycle| cycle.nodes.first() == cycle.nodes.last() && cycle.edges.contains(&edge)))]
    fn cycle_from(
        scratch: &Scratch,
        edge: EdgeId,
        last: NodeId,
    ) -> Result<CycleWitness, MaintenanceError>
    {
        let mut walk: Vec<NodeId> = alloc::vec![last];
        let mut cursor = last;
        let mut remaining = scratch.forward_parent.len();
        while cursor != edge.target {
            let index = Self::index_of(cursor)?;
            let parent = scratch
                .forward_parent
                .get(usize::from(index))
                .copied()
                .ok_or(MaintenanceError::NodeCapacity)?;
            walk.push(parent);
            cursor = parent;
            remaining = remaining
                .checked_sub(1)
                .ok_or(MaintenanceError::OrderDesynchronized)?;
        }
        walk.reverse();
        walk.push(edge.source);
        walk.push(edge.target);
        let mut edges: Vec<EdgeId> = Vec::new();
        let mut previous: Option<NodeId> = None;
        for &node in &walk {
            if let Some(source) = previous {
                edges.push(EdgeId::new(source, node));
            }
            previous = Some(node);
        }
        return Ok(CycleWitness { nodes: walk, edges });
    }

    /// The nodes of `region`, ordered as the standing order already orders
    /// them.
    ///
    /// The standing order is a topological order of the admitted edges, so
    /// sorting a set by it *is* a topological sort of that set — which is what
    /// the relocation needs, and it needs no traversal to obtain.
    ///
    /// # Errors
    /// Returns [`MaintenanceError::NodeCapacity`] when a node addresses no
    /// maintained slot, or [`MaintenanceError::OrderDesynchronized`] when a
    /// tracked handle no longer resolves — checked up front so the sort's
    /// comparator is a total order.
    ///
    /// # Specification
    /// - ensures: Sorts the supplied region by the standing order, retaining
    ///   every node.
    /// - fails: returns `NodeCapacity` for an unknown node,
    ///   `OrderDesynchronized` for a stale handle, or an index error.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 differential streams and L3 boundaries distinguish
    ///   wrong verdicts, lost edges and invalid maintained state on finite
    ///   graphs.
    /// - witness: `maintenance::tests::the_maintained_order_is_topological`
    #[inline]
    #[spec(ensures: |ret| ret.is_err() || (sorted.len() == region.len() && sorted.windows(2).all(|pair| match *pair { [(_, left), (_, right)] => self.order.cmp(left, right).is_some_and(core::cmp::Ordering::is_le), _ => true })))]
    fn sorted_by_order(
        &self,
        region: &[NodeId],
        sorted: &mut Vec<(NodeId, Pos)>,
    ) -> Result<(), MaintenanceError>
    {
        sorted.clear();
        for &node in region {
            let position = self.position(node)?;
            if self.order.get(position).is_none() {
                return Err(MaintenanceError::OrderDesynchronized);
            }
            sorted.push((node, position));
        }
        sorted.sort_unstable_by(|&(_, left), &(_, right)| {
            self.order.cmp(left, right).unwrap_or(Ordering::Equal)
        });
        return Ok(());
    }

    /// Relocates the affected region into the order positions it already
    /// occupies, backward set first and forward set after it.
    ///
    /// Each set keeps its own internal order, which the standing order already
    /// makes topological; placing the whole backward set before the whole
    /// forward set is what the new edge demands, and no edge runs from the
    /// forward set to the backward set — such an edge would have made the
    /// insertion cycle-closing, which the search reports instead.
    ///
    /// # Errors
    /// Returns [`MaintenanceError`] as [`AcyclicityMaintenance::insert_edge`]
    /// enumerates.
    ///
    /// # Specification
    /// - ensures: Places backward nodes before forward nodes within their
    ///   occupied slots.
    /// - fails: propagates order insertion/removal, missing-node, stale-handle,
    ///   and index errors.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 differential streams and L3 boundaries distinguish
    ///   wrong verdicts, lost edges and invalid maintained state on finite
    ///   graphs.
    /// - witness: `maintenance::tests::the_maintained_order_is_topological`
    #[inline]
    #[spec(ensures: |ret| ret.is_err() || bool::from(self.order_is_topological()))]
    fn relocate(
        &mut self,
        scratch: &mut Scratch,
    ) -> Result<(), MaintenanceError>
    {
        // The backward and forward sets are disjoint whenever no cycle was
        // found: a node in both would put the edge's target on a path to its
        // source, which the forward search reports as a cycle instead.
        debug_assert!(
            scratch
                .backward_region
                .iter()
                .all(|node| !scratch.forward_region.contains(node)),
            "an acyclic insertion leaves the two searched sets disjoint"
        );
        self.sorted_by_order(&scratch.backward_region, &mut scratch.backward_sorted)?;
        self.sorted_by_order(&scratch.forward_region, &mut scratch.forward_sorted)?;
        scratch.arrangement.clear();
        scratch.arrangement.extend(
            scratch
                .backward_sorted
                .iter()
                .chain(&scratch.forward_sorted)
                .map(|&(node, _position)| node),
        );
        self.sorted_by_order(&scratch.arrangement, &mut scratch.slots)?;

        // Each slot's anchor is the nearest element before it that is not
        // itself a slot; consecutive slots share one anchor, which is what
        // keeps unaffected neighbours between the slots exactly where they are.
        scratch.anchors.clear();
        let mut previous: Option<(Pos, Option<Pos>)> = None;
        for &(_, slot) in &scratch.slots {
            let candidate = self.order.prev(slot);
            let anchor = match (candidate, previous) {
                | (Some(before), Some((previous_slot, previous_anchor)))
                    if before == previous_slot =>
                {
                    previous_anchor
                },
                | _ => candidate,
            };
            scratch.anchors.push(anchor);
            previous = Some((slot, anchor));
        }

        for &(_, slot) in &scratch.slots {
            let removed = self.order.remove(slot)?;
            removed.ok_or(MaintenanceError::OrderDesynchronized)?;
        }

        let mut placed: Option<(Option<Pos>, Pos)> = None;
        for (index, &node) in scratch.arrangement.iter().enumerate() {
            let anchor = scratch.anchors.get(index).copied().flatten();
            let attach = match placed {
                | Some((previous_anchor, previous_position)) if previous_anchor == anchor => {
                    Some(previous_position)
                },
                | _ => anchor,
            };
            let fresh = match attach {
                | Some(after) => self.order.insert_after(after, node)?,
                | None => self.order.push_front(node)?,
            };
            let node_index = Self::index_of(node)?;
            let entry = self
                .positions
                .get_mut(usize::from(node_index))
                .ok_or(MaintenanceError::NodeCapacity)?;
            *entry = fresh;
            placed = Some((anchor, fresh));
            self.telemetry.nodes_relocated = self.telemetry.nodes_relocated.saturating_increment();
        }
        return Ok(());
    }
}

impl EdgeSource for AcyclicityMaintenance
{
    type Successors<'successors>
        = core::iter::Copied<core::slice::Iter<'successors, NodeId>>
    where
        Self: 'successors;

    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn node_count(&self) -> NodeCount
    {
        return self.nodes();
    }

    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn successors(
        &self,
        node: NodeId,
    ) -> Self::Successors<'_>
    {
        let empty: &[NodeId] = &[];
        return Self::index_of(node)
            .ok()
            .and_then(|index| self.successors.get(usize::from(index)))
            .map_or(empty, Vec::as_slice)
            .iter()
            .copied();
    }
}

impl core::fmt::Display for MaintenanceError
{
    /// Render the failed maintenance operation.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// Propagates a formatting sink failure.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        match *self {
            | Self::Order(error) => write!(f, "order maintenance: {error}"),
            | Self::NodeCapacity => f.write_str("node capacity"),
            | Self::OrderDesynchronized => f.write_str("order desynchronized"),
            | Self::ArithmeticOverflow => f.write_str("arithmetic overflow"),
        }
    }
}

impl core::error::Error for MaintenanceError
{
}

impl From<OrderError> for MaintenanceError
{
    /// Preserve the underlying order failure.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(error: OrderError) -> Self
    {
        Self::Order(error)
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec;
    use alloc::vec::Vec;

    use gandr_theory_graphs::EdgeId;
    use gandr_theory_graphs::NodeId;
    use gandr_theory_graphs::cycle_witness;

    use super::AcyclicityMaintenance;
    use super::EdgeVerdict;

    /// A node identifier from a small dense index.
    ///
    /// # Specification
    /// trivial.
    fn node<Index>(index: Index) -> NodeId
    where
        Index: Into<NodeId>,
    {
        index.into()
    }

    /// A directed edge from two small dense indices.
    ///
    /// # Specification
    /// trivial.
    fn edge<Source, Target>(
        source: Source,
        target: Target,
    ) -> EdgeId
    where
        Source: Into<NodeId>,
        Target: Into<NodeId>,
    {
        EdgeId::new(source.into(), target.into())
    }

    /// A structure holding exactly the offered edges that were admitted.
    ///
    /// # Specification
    /// trivial.
    fn admit(offers: &[EdgeId]) -> AcyclicityMaintenance
    {
        let mut structure = AcyclicityMaintenance::new().expect("a fresh structure is available");
        for &offer in offers {
            structure
                .insert_edge(offer)
                .expect("insertion is total over well-formed identifiers");
        }
        structure
    }

    #[test]
    fn an_edge_the_order_witnesses_is_admitted_without_moving_anything()
    {
        let mut structure = AcyclicityMaintenance::new().expect("a fresh structure is available");
        // Creating the nodes in ascending order already orders 0 before 1.
        structure
            .ensure_node(node(1u32))
            .expect("nodes are creatable");
        let verdict = structure
            .insert_edge(edge(0u32, 1u32))
            .expect("insertion succeeds");
        assert_eq!(EdgeVerdict::Admitted, verdict, "the order already agreed");
        assert_eq!(
            0,
            u64::from(structure.telemetry().nodes_relocated),
            "an admitted edge the order witnesses moves nothing"
        );
        assert_eq!(
            0,
            u64::from(structure.telemetry().nodes_visited),
            "an admitted edge the order witnesses searches nothing"
        );
    }

    #[test]
    fn a_violating_edge_is_repaired_locally()
    {
        let mut structure = AcyclicityMaintenance::new().expect("a fresh structure is available");
        structure
            .ensure_node(node(3u32))
            .expect("nodes are creatable");
        // The order is 0, 1, 2, 3; the edge 2 -> 1 runs against it.
        let verdict = structure
            .insert_edge(edge(2u32, 1u32))
            .expect("insertion succeeds");
        assert_eq!(
            EdgeVerdict::AdmittedAfterRepair,
            verdict,
            "the order had to change"
        );
        assert_eq!(
            vec![node(0u32), node(2u32), node(1u32), node(3u32)],
            structure.nodes_in_order().collect::<Vec<_>>(),
            "only the two affected nodes swapped, and the untouched ones kept their slots"
        );
        assert!(
            bool::from(structure.order_is_topological()),
            "the repaired order is topological"
        );
    }

    #[test]
    fn a_cycle_closing_edge_is_refused_with_its_walk()
    {
        let mut structure = admit(&[edge(0u32, 1u32), edge(1u32, 2u32)]);
        let verdict = structure
            .insert_edge(edge(2u32, 0u32))
            .expect("insertion succeeds");
        let EdgeVerdict::Refused(witness) = verdict
        else {
            panic!("closing 0 -> 1 -> 2 -> 0 is a cycle");
        };
        assert_eq!(
            witness.nodes.first(),
            witness.nodes.last(),
            "the witness walk is closed"
        );
        assert_eq!(
            vec![node(0u32), node(1u32), node(2u32), node(0u32)],
            witness.nodes,
            "the walk runs the cycle the offer would close"
        );
        assert_eq!(
            2,
            u64::from(structure.admitted_edges()),
            "a refused edge is not recorded"
        );
        assert!(
            bool::from(structure.order_is_topological()),
            "a refusal leaves the order intact"
        );
    }

    #[test]
    fn a_self_loop_is_refused()
    {
        let mut structure = AcyclicityMaintenance::new().expect("a fresh structure is available");
        let verdict = structure
            .insert_edge(edge(0u32, 0u32))
            .expect("insertion succeeds");
        let EdgeVerdict::Refused(witness) = verdict
        else {
            panic!("a self loop is a cycle");
        };
        assert_eq!(
            vec![node(0u32), node(0u32)],
            witness.nodes,
            "the walk is the loop"
        );
        assert_eq!(
            0,
            u64::from(structure.admitted_edges()),
            "a self loop is not recorded"
        );
    }

    #[test]
    fn a_repeated_edge_is_admitted_once()
    {
        let mut structure = admit(&[edge(0u32, 1u32), edge(0u32, 1u32), edge(0u32, 1u32)]);
        assert_eq!(
            1,
            u64::from(structure.admitted_edges()),
            "a repeat does not grow the edge set"
        );
        assert_eq!(
            3,
            u64::from(structure.telemetry().insertions),
            "every offer is counted"
        );
        let verdict = structure
            .insert_edge(edge(0u32, 1u32))
            .expect("insertion succeeds");
        assert_eq!(EdgeVerdict::Admitted, verdict, "a repeat is still admitted");
    }

    #[test]
    fn the_maintained_order_is_topological()
    {
        let structure = admit(&[
            edge(4u32, 3u32),
            edge(3u32, 2u32),
            edge(2u32, 1u32),
            edge(1u32, 0u32),
            edge(4u32, 0u32),
        ]);
        assert!(
            bool::from(structure.order_is_topological()),
            "a reversing chain is fully repaired"
        );
        assert_eq!(
            vec![node(4u32), node(3u32), node(2u32), node(1u32), node(0u32)],
            structure.nodes_in_order().collect::<Vec<_>>(),
            "the chain ends up exactly reversed"
        );
        assert_eq!(
            None,
            cycle_witness(&structure).expect("the dense graph is well formed"),
            "the admitted graph is acyclic"
        );
    }

    #[test]
    fn a_corrupted_order_is_caught_by_the_invariant()
    {
        // The seeded corruption the differential must have teeth against:
        // the admitted edges are left alone and the maintained order is
        // rewritten behind the structure's back, so nothing but the invariant
        // query can notice.
        let mut structure = admit(&[edge(0u32, 1u32), edge(1u32, 2u32)]);
        assert!(
            bool::from(structure.order_is_topological()),
            "the structure starts sound"
        );

        let head = structure.order.first().expect("the order is non-empty");
        let displaced = structure
            .order
            .remove(head)
            .expect("removal succeeds")
            .expect("the head is removable");
        let tail = structure
            .order
            .last()
            .expect("the order is still non-empty");
        let moved = structure
            .order
            .insert_after(tail, displaced)
            .expect("reinsertion succeeds");
        let index = AcyclicityMaintenance::index_of(displaced).expect("the node is addressable");
        *structure
            .positions
            .get_mut(usize::from(index))
            .expect("the node has a slot") = moved;

        assert!(
            !bool::from(structure.order_is_topological()),
            "moving a source behind its target is caught"
        );
    }

    #[test]
    fn a_refusal_leaves_the_structure_usable()
    {
        let mut structure = admit(&[edge(0u32, 1u32), edge(1u32, 2u32)]);
        let refused = structure
            .insert_edge(edge(2u32, 0u32))
            .expect("insertion succeeds");
        assert!(
            matches!(refused, EdgeVerdict::Refused(_)),
            "the offer closes a cycle"
        );
        let admitted = structure
            .insert_edge(edge(0u32, 2u32))
            .expect("insertion succeeds");
        assert_eq!(
            EdgeVerdict::Admitted,
            admitted,
            "the structure keeps working after a refusal"
        );
        assert!(
            bool::from(structure.order_is_topological()),
            "and stays sound"
        );
    }

    #[test]
    fn unaffected_nodes_between_the_endpoints_keep_their_slots()
    {
        // Nodes 1 and 2 sit between the endpoints in the order but neither
        // reaches 4 nor is reached by 3, so the repair must step over them.
        let mut structure = AcyclicityMaintenance::new().expect("a fresh structure is available");
        structure
            .ensure_node(node(4u32))
            .expect("nodes are creatable");
        let verdict = structure
            .insert_edge(edge(3u32, 0u32))
            .expect("insertion succeeds");
        assert_eq!(
            EdgeVerdict::AdmittedAfterRepair,
            verdict,
            "the order had to change"
        );
        assert_eq!(
            vec![node(3u32), node(1u32), node(2u32), node(0u32), node(4u32)],
            structure.nodes_in_order().collect::<Vec<_>>(),
            "the two affected nodes exchanged their own slots and nothing else moved"
        );
        assert!(
            bool::from(structure.order_is_topological()),
            "the repaired order is topological"
        );
    }
}
