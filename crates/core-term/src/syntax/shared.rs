//! Certificate syntax compared as the graph it is shared as, in time linear in
//! the nodes the two sides reach.
//!
//! [`super::equal_syntax`] memoises the pairs it meets, so two sides that share
//! one subterm differently meet it in as many pairs as their copies align:
//! quadratic in the worst case, with an ordered set's logarithm on each pair.
//! This module decides the same relation by Paterson and Wegman's unification,
//! in the form Condoluci, Accattoli and Sacerdoti Coen give it for λ-graphs:
//! the blind check. Every node the two roots reach joins one class. A class is
//! built from the queries that name its members, and a member is dequeued only
//! once every parent of it stands in a closed class, so every query naming it
//! is posed by then. A parent in a class still open is a cycle up to the query,
//! and the sides differ. Once a class closes, each member is checked against
//! the class's first node by [`super::pair_step`], which poses the queries on
//! their children. Bound variables are de Bruijn indices, so α-equivalence is
//! syntactic and the paper's variables check has nothing to do.
//!
//! The state lives for one comparison: dense tables indexed by each reached
//! node's offset in its family, each node's parents laid out once, and the
//! queries as linked lists in two arrays. A class whose building waits on a
//! parent's class is a frame on an explicit stack, every frame's queue a
//! segment of one vector, so the paper's recursion uses no call stack. The
//! dense tables grow to the largest offset reached, so the check suits an
//! arena that holds the two sides and little else, as the tier's reading
//! arena does; a comparison of two small sides in a large arena is the
//! pairwise walk's.
//!
//! # References
//!
//! - `vault:01a18584-cd93-7e42-9b53-9deb10b838fc` — exemplar: Condoluci,
//!   Accattoli and Sacerdoti Coen's blind check, Algorithm 1, linear in the
//!   graph and the query (Theorem 7.2). The module runs it over the arena's
//!   children, with the former comparison as each node's label.

use alloc::borrow::Cow;
use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;

use super::CertificateEquality;
use super::Reading;
use super::StructuralGoal;
use super::pair_step;
use crate::arena::CompTypeId;
use crate::arena::ComputationId;
use crate::arena::CoreArena;
use crate::arena::ValueId;
use crate::arena::ValueTypeId;
use crate::children;
use crate::children::Visit;
use crate::support::Crossing;

/// More reached nodes or posed queries than a number counts.
struct Overflow;

/// A reached node's number: its row in each table one comparison keeps.
#[repr(transparent)]
#[derive(Clone, Copy, Default, Eq, PartialEq)]
struct Number(u32);

impl Number
{
    /// No node: an unset entry of a table.
    const NONE: Self = Self(u32::MAX);
}

impl From<Number> for usize
{
    /// The row `number` names in a table.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(number: Number) -> Self
    {
        Self::try_from(number.0).unwrap_or(Self::MAX)
    }
}

impl TryFrom<usize> for Number
{
    type Error = Overflow;

    /// The number of the node at `row`, or [`Overflow`] from the number that
    /// stands for no node on.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn try_from(row: usize) -> Result<Self, Overflow>
    {
        u32::try_from(row)
            .ok()
            .filter(|&raw| raw != u32::MAX)
            .map(Self)
            .ok_or(Overflow)
    }
}

/// A posed query's half-edge: its row in the queries' tables.
#[repr(transparent)]
#[derive(Clone, Copy, Eq, PartialEq)]
struct HalfEdge(u32);

impl HalfEdge
{
    /// No half-edge: the end of a node's list.
    const NONE: Self = Self(u32::MAX);
}

impl From<HalfEdge> for usize
{
    /// The row `edge` names in the queries' tables.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(edge: HalfEdge) -> Self
    {
        Self::try_from(edge.0).unwrap_or(Self::MAX)
    }
}

impl TryFrom<usize> for HalfEdge
{
    type Error = Overflow;

    /// The half-edge at `row`, or [`Overflow`] from the half-edge that stands
    /// for none on.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn try_from(row: usize) -> Result<Self, Overflow>
    {
        u32::try_from(row)
            .ok()
            .filter(|&raw| raw != u32::MAX)
            .map(Self)
            .ok_or(Overflow)
    }
}

/// A node the two roots reach, by family.
#[derive(Clone, Copy)]
enum Node
{
    /// A value.
    Value(ValueId),
    /// A computation.
    Computation(ComputationId),
    /// A value type.
    ValueType(ValueTypeId),
    /// A computation type.
    CompType(CompTypeId),
}

/// A node's number, and whether numbering it gave it the number.
#[derive(Clone, Copy)]
enum Numbered
{
    /// The node had no number, and now has this one.
    Fresh(Number),
    /// The node already had this number.
    Known(Number),
}

/// The number of each reached node: one dense table per family, indexed by
/// the node's offset in its family and grown to the largest offset reached,
/// [`Number::NONE`] where no node is numbered; and the reached nodes.
#[derive(Default)]
struct Numbering
{
    /// The values' numbers.
    values: Vec<Number>,
    /// The computations' numbers.
    computations: Vec<Number>,
    /// The value types' numbers.
    value_types: Vec<Number>,
    /// The computation types' numbers.
    comp_types: Vec<Number>,
    /// The reached nodes, by number.
    nodes: Vec<Node>,
}

impl Numbering
{
    /// The number `node` was given, when it was.
    ///
    /// # Specification
    /// trivial.
    fn get(
        &self,
        node: Node,
    ) -> Option<Number>
    {
        let (table, offset) = match node {
            Node::Value(id) => (&self.values, id.offset()),
            Node::Computation(id) => (&self.computations, id.offset()),
            Node::ValueType(id) => (&self.value_types, id.offset()),
            Node::CompType(id) => (&self.comp_types, id.offset()),
        };
        table
            .get(usize::from(offset))
            .copied()
            .filter(|&number| number != Number::NONE)
    }

    /// `node`'s number, giving it the next one when it has none; [`Overflow`]
    /// when more nodes are reached than a number counts.
    ///
    /// # Specification
    /// trivial.
    fn number(
        &mut self,
        node: Node,
    ) -> Result<Numbered, Overflow>
    {
        let next = Number::try_from(self.nodes.len())?;
        let (table, offset) = match node {
            Node::Value(id) => (&mut self.values, id.offset()),
            Node::Computation(id) => (&mut self.computations, id.offset()),
            Node::ValueType(id) => (&mut self.value_types, id.offset()),
            Node::CompType(id) => (&mut self.comp_types, id.offset()),
        };
        let row = usize::from(offset);
        if table.len() <= row {
            table.resize(row.saturating_add(1), Number::NONE);
        }
        let entry = table.get_mut(row).ok_or(Overflow)?;
        if *entry != Number::NONE {
            return Ok(Numbered::Known(*entry));
        }
        *entry = next;
        self.nodes.push(node);
        Ok(Numbered::Fresh(next))
    }

    /// The node numbered `number`.
    ///
    /// # Specification
    /// trivial.
    fn node(
        &self,
        number: Number,
    ) -> Option<Node>
    {
        self.nodes.get(usize::from(number)).copied()
    }

    /// The numbers of a pair's two nodes, when both were given one.
    ///
    /// # Specification
    /// trivial.
    fn pair(
        &self,
        goal: StructuralGoal,
    ) -> Option<(Number, Number)>
    {
        let (left, right) = match goal {
            StructuralGoal::Value(left, right) => (Node::Value(left), Node::Value(right)),
            StructuralGoal::Computation(left, right) => {
                (Node::Computation(left), Node::Computation(right))
            },
            StructuralGoal::ValueType(left, right) => {
                (Node::ValueType(left), Node::ValueType(right))
            },
            StructuralGoal::CompType(left, right) => (Node::CompType(left), Node::CompType(right)),
        };
        Some((self.get(left)?, self.get(right)?))
    }
}

/// The walk that numbers every node the two roots reach and records each edge
/// from a child to its parent.
#[derive(Default)]
struct Reach
{
    /// Each reached node's number, and the reached nodes by number.
    numbering: Numbering,
    /// Each edge, as its child's number beside its parent's.
    edges: Vec<(Number, Number)>,
    /// The nodes numbered and not yet expanded.
    unexpanded: Vec<Number>,
    /// The node whose children are being visited.
    parent: Number,
    /// Whether more nodes were reached than a number can count.
    overflowed: bool,
}

impl Reach
{
    /// `node`'s number, numbering it, and queueing it for expansion, when it
    /// has none yet; [`Number::NONE`] once more nodes are reached than a
    /// number counts.
    ///
    /// # Specification
    /// trivial.
    fn number(
        &mut self,
        node: Node,
    ) -> Number
    {
        match self.numbering.number(node) {
            Ok(Numbered::Fresh(number)) => {
                self.unexpanded.push(number);
                number
            },
            Ok(Numbered::Known(number)) => number,
            Err(Overflow) => {
                self.overflowed = true;
                Number::NONE
            },
        }
    }

    /// Record `node` as a child of the node being expanded.
    ///
    /// # Specification
    /// trivial.
    fn child(
        &mut self,
        node: Node,
    )
    {
        let child = self.number(node);
        if child != Number::NONE {
            self.edges.push((child, self.parent));
        }
    }
}

impl Visit for Reach
{
    /// Record a value child.
    ///
    /// # Specification
    /// trivial.
    fn value(
        &mut self,
        child: ValueId,
        _crossing: Crossing,
    )
    {
        self.child(Node::Value(child));
    }

    /// Record a computation child.
    ///
    /// # Specification
    /// trivial.
    fn computation(
        &mut self,
        child: ComputationId,
        _crossing: Crossing,
    )
    {
        self.child(Node::Computation(child));
    }

    /// Record a value-type child.
    ///
    /// # Specification
    /// trivial.
    fn value_type(
        &mut self,
        child: ValueTypeId,
        _crossing: Crossing,
    )
    {
        self.child(Node::ValueType(child));
    }

    /// Record a computation-type child.
    ///
    /// # Specification
    /// trivial.
    fn comp_type(
        &mut self,
        child: CompTypeId,
        _crossing: Crossing,
    )
    {
        self.child(Node::CompType(child));
    }
}

/// The queries posed so far, undirected: each node's as a linked list of
/// half-edges.
struct Queries
{
    /// Each node's first half-edge, or [`HalfEdge::NONE`].
    head: Vec<HalfEdge>,
    /// Each half-edge's far end.
    to: Vec<Number>,
    /// Each half-edge's next half-edge from the same node, or
    /// [`HalfEdge::NONE`].
    next: Vec<HalfEdge>,
}

impl Queries
{
    /// No query, over the nodes `numbering` numbered.
    ///
    /// # Specification
    /// trivial.
    fn new(numbering: &Numbering) -> Self
    {
        Self {
            head: vec![HalfEdge::NONE; numbering.nodes.len()],
            to: Vec::new(),
            next: Vec::new(),
        }
    }

    /// Pose the query that `left` and `right` agree: each end lists the other
    /// first, unless the two are one node; [`Overflow`] once more half-edges
    /// are posed than a number counts.
    ///
    /// # Specification
    /// trivial.
    fn pose(
        &mut self,
        left: Number,
        right: Number,
    ) -> Result<(), Overflow>
    {
        if left == right {
            return Ok(());
        }
        for (from, far) in [(left, right), (right, left)] {
            let edge = HalfEdge::try_from(self.to.len())?;
            let head = self.head.get_mut(usize::from(from)).ok_or(Overflow)?;
            self.to.push(far);
            self.next.push(*head);
            *head = edge;
        }
        Ok(())
    }

    /// The first half-edge `node` lists, or [`HalfEdge::NONE`].
    ///
    /// # Specification
    /// trivial.
    fn first(
        &self,
        node: Number,
    ) -> HalfEdge
    {
        self.head
            .get(usize::from(node))
            .copied()
            .unwrap_or(HalfEdge::NONE)
    }

    /// The far end of `edge`, beside the next half-edge from the same node.
    ///
    /// # Specification
    /// trivial.
    fn follow(
        &self,
        edge: HalfEdge,
    ) -> Option<(Number, HalfEdge)>
    {
        let row = usize::from(edge);
        Some((*self.to.get(row)?, *self.next.get(row)?))
    }
}

/// A class being built: its first node, and its members' segment of the
/// shared queue.
#[derive(Clone, Copy)]
struct Frame
{
    /// The class's first node, the one each member is checked against.
    canonic: Number,
    /// Where the class's members start in the queue.
    base: usize,
    /// The next member to dequeue.
    cursor: usize,
}

/// Decide whether `left` and `right` agree as [`super::equal_syntax`] decides
/// it under [`Reading::Syntax`], in time linear in the nodes they reach.
///
/// # Specification
/// - ensures: [`CertificateEquality::Equal`] exactly when the smallest
///   equivalence over the reached nodes that relates `left` to `right` and, for
///   every pair it relates, the children [`super::pair_step`] pairs, has every
///   related pair accepted by [`super::pair_step`]. That is the relation
///   [`super::equal_syntax`] decides, since the arena is acyclic.
/// - fails: [`CertificateEquality::Different`] on a dangling node, and on more
///   reached nodes or posed queries than a `u32` counts.
/// - panics: none.
/// - executable: none — [`super::equal_shared_certificate_syntax`], the one
///   caller, holds every verdict to the pairwise walk's on every enforcing
///   call.
///
/// # Termination
/// - reason: the reaching walk expands each numbered node once; each frame
///   dequeues each member once and scans each member's parents once; a frame
///   opens only for a node with no class, and gives it one.
/// - measure: the reached nodes not yet expanded, then the members not yet
///   dequeued plus the parent entries not yet scanned plus the nodes with no
///   class.
///
/// # Adequacy
/// - hypothesis: L3 — sides sharing one subterm differently, every former's
///   twin and each guarded part's breach, each decided beside the pairwise
///   walk.
/// - witness: `syntax::tests::sides_shared_differently_agree_until_one_copy_differs`
/// - witness: `syntax::tests::each_value_former_equals_its_twin_and_differs_where_its_guard_does`
/// - witness: `syntax::tests::each_computation_former_equals_its_twin_and_differs_where_its_guard_does`
pub(super) fn equal(
    arena: &CoreArena,
    left: ValueId,
    right: ValueId,
) -> CertificateEquality
{
    let mut reach = Reach::default();
    let left = reach.number(Node::Value(left));
    let right = reach.number(Node::Value(right));
    while let Some(next) = reach.unexpanded.pop() {
        reach.parent = next;
        let Some(node) = reach.numbering.node(next)
        else {
            return CertificateEquality::Different;
        };
        let expanded = match node {
            Node::Value(id) => arena
                .value(id)
                .map(|value| children::of_value(value, &mut reach)),
            Node::Computation(id) => arena
                .computation(id)
                .map(|computation| children::of_computation(computation, &mut reach)),
            Node::ValueType(id) => arena
                .value_type(id)
                .map(|value_type| children::of_value_type(value_type, &mut reach)),
            Node::CompType(id) => arena
                .comp_type(id)
                .map(|comp_type| children::of_comp_type(comp_type, &mut reach)),
        };
        if expanded.is_none() {
            return CertificateEquality::Different;
        }
    }
    if reach.overflowed {
        return CertificateEquality::Different;
    }
    if left == right {
        return CertificateEquality::Equal;
    }
    let Reach {
        numbering, edges, ..
    } = reach;
    let count = numbering.nodes.len();

    // Each node's parents, laid out once: `starts[n] .. starts[n + 1]` holds
    // node `n`'s.
    let mut starts = vec![0_usize; count.saturating_add(1)];
    for &(child, _) in &edges {
        if let Some(start) = starts.get_mut(usize::from(child)) {
            *start = start.saturating_add(1);
        }
    }
    let mut running = 0_usize;
    for start in &mut starts {
        running = running.saturating_add(*start);
        *start = running;
    }
    let mut parents = vec![Number::NONE; edges.len()];
    for &(child, parent) in &edges {
        if let Some(start) = starts.get_mut(usize::from(child)) {
            *start = start.saturating_sub(1);
            if let Some(slot) = parents.get_mut(*start) {
                *slot = parent;
            }
        }
    }

    let mut queries = Queries::new(&numbering);
    if queries.pose(left, right).is_err() {
        return CertificateEquality::Different;
    }
    let mut canonic = vec![Number::NONE; count];
    let mut closed = vec![false; count];
    let mut scanned = starts
        .get(.. count)
        .map_or_else(Vec::new, <[usize]>::to_vec);
    let mut queue: Vec<Number> = Vec::new();
    let mut frames: Vec<Frame> = Vec::new();
    let mut posed: Vec<StructuralGoal> = Vec::new();
    let unread = BTreeMap::new();
    let mut syntax = Cow::Borrowed(arena);

    for row in 0 .. count {
        if canonic.get(row).is_none_or(|&class| class != Number::NONE) {
            continue;
        }
        let Ok(first) = Number::try_from(row)
        else {
            return CertificateEquality::Different;
        };
        let mut opening = Some(first);
        loop {
            if let Some(opened) = opening.take() {
                if let Some(class) = canonic.get_mut(usize::from(opened)) {
                    *class = opened;
                }
                frames.push(Frame {
                    canonic: opened,
                    base: queue.len(),
                    cursor: queue.len(),
                });
                queue.push(opened);
            }
            let Some(&Frame {
                canonic: class,
                base,
                cursor,
            }) = frames.last()
            else {
                break;
            };
            if let Some(&member) = queue.get(cursor) {
                // Parents first: every parent of the member stands in a closed
                // class before the member is dequeued.
                let end = starts
                    .get(usize::from(member).saturating_add(1))
                    .copied()
                    .unwrap_or_default();
                let Some(scan) = scanned.get_mut(usize::from(member))
                else {
                    return CertificateEquality::Different;
                };
                while *scan < end {
                    let parent = parents.get(*scan).copied().unwrap_or(Number::NONE);
                    *scan = scan.saturating_add(1);
                    match canonic.get(usize::from(parent)).copied() {
                        Some(Number::NONE) => {
                            opening = Some(parent);
                            break;
                        },
                        Some(owner)
                            if closed.get(usize::from(owner)).copied().unwrap_or_default() => {},
                        // A parent in a class still open is a cycle up to the
                        // query.
                        _ => return CertificateEquality::Different,
                    }
                }
                if opening.is_some() {
                    continue;
                }
                if let Some(top) = frames.last_mut() {
                    top.cursor = cursor.saturating_add(1);
                }
                let mut edge = queries.first(member);
                while edge != HalfEdge::NONE {
                    let Some((other, next)) = queries.follow(edge)
                    else {
                        return CertificateEquality::Different;
                    };
                    match canonic.get_mut(usize::from(other)) {
                        Some(owner) if *owner == Number::NONE => {
                            *owner = class;
                            queue.push(other);
                        },
                        Some(owner) if *owner == class => {},
                        _ => return CertificateEquality::Different,
                    }
                    edge = next;
                }
                continue;
            }
            // The class is complete: check each member against its first node
            // and pose the queries on their children.
            if let Some(flag) = closed.get_mut(usize::from(class)) {
                *flag = true;
            }
            let Some(canonic_node) = numbering.node(class)
            else {
                return CertificateEquality::Different;
            };
            for &member in queue.get(base.saturating_add(1) ..).unwrap_or_default() {
                let Some(member_node) = numbering.node(member)
                else {
                    return CertificateEquality::Different;
                };
                let goal = match (canonic_node, member_node) {
                    (Node::Value(a), Node::Value(b)) => StructuralGoal::Value(a, b),
                    (Node::Computation(a), Node::Computation(b)) => {
                        StructuralGoal::Computation(a, b)
                    },
                    (Node::ValueType(a), Node::ValueType(b)) => StructuralGoal::ValueType(a, b),
                    (Node::CompType(a), Node::CompType(b)) => StructuralGoal::CompType(a, b),
                    _ => return CertificateEquality::Different,
                };
                if pair_step(&mut syntax, Reading::Syntax, &unread, goal, &mut posed)
                    == CertificateEquality::Different
                {
                    return CertificateEquality::Different;
                }
                while let Some(pair) = posed.pop() {
                    let Some((a, b)) = numbering.pair(pair)
                    else {
                        return CertificateEquality::Different;
                    };
                    if queries.pose(a, b).is_err() {
                        return CertificateEquality::Different;
                    }
                }
            }
            queue.truncate(base);
            frames.pop();
        }
    }
    CertificateEquality::Equal
}
