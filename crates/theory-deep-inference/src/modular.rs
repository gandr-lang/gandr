//! The modular decomposition of a causal web: its events as a tree of
//! independent, ordered and prime compositions.
//!
//! A module of a strict partial order is a set of events every other event
//! treats alike: it precedes all of them, follows all of them, or is
//! independent of all of them. [`DependenceBits::decompose`] builds the tree
//! of the order's strong modules. A [`ModularNode::Par`] holds factors no event
//! of which is ordered with an event of another. A [`ModularNode::Seq`] holds
//! factors in total precedence, earliest first. A [`ModularNode::Prime`] holds
//! factors no proper union of which is a module, with the precedence between
//! them as its quotient. Events stand at the leaves.
//!
//! The tree is a function of the order. A parallel or prime node's factors
//! stand in the order of their least vertex, and a series node's in
//! precedence, so [`ModularTree::relation`] reads every pair back exactly. The
//! parallel and series parts are canonical by construction, and only a prime
//! node's quotient carries the order's residual shape. A web with no prime node
//! is series-parallel.
//!
//! # Decomposition
//!
//! A strong module splits three ways. Its comparability graph disconnected,
//! the components are a [`ModularNode::Par`]'s factors. Its incomparability
//! graph disconnected, the co-components are totally ordered, and they are a
//! [`ModularNode::Seq`]'s factors. Both graphs connected, the maximal proper
//! modules partition it, and they are a [`ModularNode::Prime`]'s. Two events
//! fall in one maximal module exactly when the module they generate is not the
//! whole, so each event's block is found by growing that closure against every
//! other. Each module is split by a worklist, never by recursion. Every
//! relation this crate builds is transitive, so the one order it refuses is a
//! cycle, named by its first vertex.
//!
//! # Witnesses
//!
//! `tests::modular` decomposes chains, antichains and their alternations, the
//! four-event N-shape that is the smallest prime order, and twin events, which
//! fall in one module. It reads every pair back from the tree of a generated
//! order, checks each prime quotient prime and each node strong, and reads two
//! dialogue webs: an exchange in which each endpoint sends and then receives
//! decomposes series-parallel, and an endpoint that moves on its own between
//! sending and receiving a crossing message leaves a prime node.
//!
//! # References
//!
//! - Tibor Gallai. "Transitiv orientierbare Graphen." _Acta Mathematica
//!   Academiae Scientiarum Hungaricae_ 18 (1967), 25–66.
//!   `doi:10.1007/BF02020961` — modules and the three-way split.
//! - Ross M. `McConnell` and Jeremy P. Spinrad. "Modular decomposition and
//!   transitive orientation." _Discrete Mathematics_ 201 (1999), 189–241.
//!   `doi:10.1016/S0012-365X(98)00319-7` — the linear-time decomposition.
//! - Matteo Acclavio. "Sequent Systems on Undirected Graphs." IJCAR 2024, LNCS
//!   14740, 216–236. `doi:10.1007/978-3-031-63501-4_12` — prime graphs as
//!   connectives, the decomposition unique up to their symmetries.

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::cmp::Ordering;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::boundary::FactorIndex;
use crate::boundary::ModuleCount;
use crate::boundary::ModuleId;
use crate::boundary::WebVertex;
use crate::boundary::WebVertexCount;
use crate::causal_web::CausalWeb;
use crate::causal_web::DependenceBits;
use crate::causal_web::WebRelation;

quenchant_shape::reason_enum! {
    /// Why a modular decomposition tree holds no node.
    pub mod module_lookup {
        /// The reason the lookup finds no node.
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub enum Absent {
            /// The decomposed order holds no event, so the tree has no root.
            Empty,
            /// The identifier is at or past the tree's node count.
            OutOfRange,
        }
    }
}

/// One node of a modular decomposition tree.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ModularNode
{
    /// One event.
    Event(WebVertex),
    /// Factors no event of which is ordered with an event of another, in the
    /// order of their least vertex.
    Par(Box<[ModuleId]>),
    /// Factors in total precedence, earliest first: every event of a factor
    /// precedes every event of each later one.
    Seq(Box<[ModuleId]>),
    /// Factors no proper union of which is a module.
    Prime
    {
        /// The factors, in the order of their least vertex.
        factors: Box<[ModuleId]>,
        /// The precedence between factors, read at one event of each, over
        /// the factors' positions.
        quotient: DependenceBits,
    },
}

/// Why a relation has no modular decomposition.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum DecompositionRefusal
{
    /// The web's relation is not square over its events.
    Malformed,
    /// The vertex precedes itself: the relation's edges close a cycle.
    Cyclic
    {
        /// The first vertex on a cycle.
        vertex: WebVertex,
    },
}

/// The modular decomposition of a strict partial order: its strong modules as
/// a tree, the root first and every node before its factors.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ModularTree
{
    /// The nodes; the root is the first.
    nodes: Box<[ModularNode]>,
    /// Each node's parent and its position among the parent's factors; the
    /// root names itself.
    parents: Box<[(ModuleId, FactorIndex)]>,
    /// Each node's number of ancestors.
    depths: Box<[ModuleCount]>,
    /// Each vertex's leaf.
    leaves: Box<[ModuleId]>,
}

impl ModularTree
{
    /// The root: the node whose events are the whole order.
    ///
    /// # Specification
    /// - ensures: the first node, or [`module_lookup::Absent::Empty`] when the
    ///   order holds no event.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the empty order has no root, and every other order's
    ///   root is the node whose leaves are all its events.
    /// - witness: `tests::modular::the_empty_order_has_no_root`
    /// - witness: `tests::modular::a_chain_is_one_series_node`
    #[inline]
    #[spec(ensures: |output| if self.nodes.is_empty() { output == Maybe::Absent(module_lookup::Absent::Empty) } else { output == Maybe::Present(ModuleId::from(0_usize)) })]
    pub fn root(&self) -> Maybe<ModuleId, module_lookup::Absent>
    {
        if self.nodes.is_empty() {
            Maybe::Absent(module_lookup::Absent::Empty)
        }
        else {
            Maybe::Present(ModuleId::from(0_usize))
        }
    }

    /// The node at `id`.
    ///
    /// # Specification
    /// - ensures: the node at `id`, or [`module_lookup::Absent::OutOfRange`]
    ///   past the node count.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a named shape's nodes are read by identifier, and an
    ///   identifier past the count reads nothing.
    /// - witness: `tests::modular::the_n_shape_is_prime`
    /// - witness: `tests::modular::the_empty_order_has_no_root`
    #[inline]
    #[spec(ensures: |output| self.nodes.get(usize::from(id)).map_or_else(|| output == Maybe::Absent(module_lookup::Absent::OutOfRange), |node| output == Maybe::Present(node)))]
    pub fn node(
        &self,
        id: ModuleId,
    ) -> Maybe<&ModularNode, module_lookup::Absent>
    {
        self.nodes.get(usize::from(id)).map_or(
            Maybe::Absent(module_lookup::Absent::OutOfRange),
            Maybe::Present,
        )
    }

    /// The number of nodes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn node_count(&self) -> ModuleCount
    {
        ModuleCount::from(self.nodes.len())
    }

    /// The number of prime nodes: zero exactly for a series-parallel order.
    ///
    /// # Specification
    /// - ensures: the count of [`ModularNode::Prime`] nodes.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — chains, antichains and their alternations hold no
    ///   prime node, and the N-shape and a dialogue with a move between a send
    ///   and a crossing receipt hold one each.
    /// - witness: `tests::modular::series_and_parallel_alternate`
    /// - witness: `tests::modular::the_n_shape_is_prime`
    /// - witness: `tests::modular::a_move_before_a_crossing_receipt_leaves_a_prime_node`
    #[inline]
    #[must_use]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body counts the same nodes"
        )
    )]
    #[spec(ensures: |output| usize::from(output) == self.nodes.iter().filter(|node| matches!(node, &&ModularNode::Prime { .. })).count())]
    pub fn prime_count(&self) -> ModuleCount
    {
        ModuleCount::from(
            self.nodes
                .iter()
                .filter(|node| matches!(node, &&ModularNode::Prime { .. }))
                .count(),
        )
    }

    /// The relation between two events, read off the tree: at the node where
    /// their leaves' paths to the root meet, independence under a parallel
    /// node, the factors' order under a series node, and the quotient under a
    /// prime one.
    ///
    /// # Specification
    /// - ensures: [`WebRelation::Missing`] for a vertex past the order or two
    ///   equal vertices; otherwise the relation of the decomposed order.
    /// - panics: none.
    /// - intension: the length of the two leaves' paths to their meeting node.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every pair of a generated order reads back as the
    ///   order relates it, and an equal or out-of-range pair reads as missing.
    /// - witness: `tests::modular::the_tree_reads_back_the_order`
    /// - witness: `tests::modular::a_chain_is_one_series_node`
    #[must_use]
    #[inline]
    #[spec(ensures: |output| (left != right && usize::from(left) < self.leaves.len() && usize::from(right) < self.leaves.len()) || output == WebRelation::Missing)]
    pub fn relation(
        &self,
        left: WebVertex,
        right: WebVertex,
    ) -> WebRelation
    {
        if left == right {
            return WebRelation::Missing;
        }
        let (Some(&leaf_left), Some(&leaf_right)) = (
            self.leaves.get(usize::from(left)),
            self.leaves.get(usize::from(right)),
        )
        else {
            return WebRelation::Missing;
        };
        let depth = |id: ModuleId| {
            self.depths
                .get(usize::from(id))
                .copied()
                .unwrap_or_default()
        };
        let up = |id: ModuleId| {
            self.parents
                .get(usize::from(id))
                .copied()
                .unwrap_or_else(|| (id, FactorIndex::from(0_usize)))
        };
        let (mut at_left, mut at_right) = (leaf_left, leaf_right);
        let (mut position_left, mut position_right) =
            (FactorIndex::default(), FactorIndex::default());
        while depth(at_left) > depth(at_right) {
            (at_left, position_left) = up(at_left);
        }
        while depth(at_right) > depth(at_left) {
            (at_right, position_right) = up(at_right);
        }
        while at_left != at_right {
            let (next_left, next_right) = (up(at_left), up(at_right));
            if next_left.0 == at_left || next_right.0 == at_right {
                return WebRelation::Missing;
            }
            (at_left, position_left) = next_left;
            (at_right, position_right) = next_right;
        }
        match self.nodes.get(usize::from(at_left)) {
            Some(&ModularNode::Par(_)) => WebRelation::Independent,
            Some(&ModularNode::Seq(_)) => {
                if position_left < position_right {
                    WebRelation::Precedes
                }
                else {
                    WebRelation::Follows
                }
            },
            Some(&ModularNode::Prime { ref quotient, .. }) => between(
                quotient,
                WebVertex::from(usize::from(position_left)),
                WebVertex::from(usize::from(position_right)),
            ),
            Some(&ModularNode::Event(_)) | None => WebRelation::Missing,
        }
    }
}

impl DependenceBits
{
    /// The modular decomposition of the order.
    ///
    /// # Specification
    /// - ensures: on success, [`ModularTree::relation`] agrees with the order
    ///   on every pair of distinct vertices; a refusal names the first vertex
    ///   that precedes itself.
    /// - panics: none.
    /// - intension: quadratic in the vertex count per tree level for a
    ///   series-parallel order; a prime node over `k` events grows a module
    ///   closure, quadratic in `k`, for every pair it separates.
    ///
    /// # Errors
    /// [`DecompositionRefusal::Cyclic`] for a vertex that precedes itself.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — chains, antichains, their alternations, the N-shape,
    ///   twins and generated orders decompose to trees that read every pair
    ///   back, whose prime quotients are prime and whose nodes are strong; a
    ///   cycle is refused by its first vertex.
    /// - witness: `tests::modular::the_tree_reads_back_the_order`
    /// - witness: `tests::modular::the_n_shape_is_prime`
    /// - witness: `tests::modular::twins_fall_in_one_module`
    /// - witness: `tests::modular::a_cycle_is_refused_by_its_first_vertex`
    #[spec(ensures: |output| output.as_ref().map_or(true, |tree| {
        let count = usize::from(self.vertex_count());
        (0 .. count).all(|left| (0 .. count).all(|right| left == right
            || tree.relation(WebVertex::from(left), WebVertex::from(right))
                == between(self, WebVertex::from(left), WebVertex::from(right))))
    }))]
    #[inline]
    pub fn decompose(&self) -> Result<ModularTree, DecompositionRefusal>
    {
        let count = self.vertex_count();
        if let Some(vertex) = (0 .. usize::from(count))
            .map(WebVertex::from)
            .find(|&vertex| bool::from(self.contains(vertex, vertex)))
        {
            return Err(DecompositionRefusal::Cyclic { vertex });
        }
        let mut builder = Builder::new(self, count);
        while let Some((slot, members)) = builder.work.pop() {
            builder.step(slot, &members);
        }
        Ok(builder.finish())
    }
}

impl CausalWeb
{
    /// The modular decomposition of the web's precedence, over its canonical
    /// vertices.
    ///
    /// # Specification
    /// - ensures: [`DecompositionRefusal::Malformed`] for a web whose relation
    ///   does not match its event list; otherwise as
    ///   [`DependenceBits::decompose`] over [`Self::precedes`].
    /// - panics: none.
    ///
    /// # Errors
    /// As [`DependenceBits::decompose`], and
    /// [`DecompositionRefusal::Malformed`] for an event list the relation does
    /// not match.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a tracelet's independent pair decomposes to one
    ///   parallel node, and an emptied event list under a two-vertex relation
    ///   is refused as malformed.
    /// - witness: `tests::modular::a_tracelet_web_decomposes_over_its_events`
    #[inline]
    #[cfg_attr(
        dylint_lib = "quenchant_dylints",
        expect(
            spec_clause_traversal,
            reason = "parity: the body checks the same shape before decomposing"
        )
    )]
    #[spec(ensures: |output| if bool::from(self.has_valid_shape()) { output == self.precedes.decompose() } else { output == Err(DecompositionRefusal::Malformed) })]
    pub fn decompose(&self) -> Result<ModularTree, DecompositionRefusal>
    {
        if !bool::from(self.has_valid_shape()) {
            return Err(DecompositionRefusal::Malformed);
        }
        self.precedes.decompose()
    }
}

/// The relation between two vertices of `bits`, independence when neither
/// precedes the other.
///
/// # Specification
/// trivial.
fn between(
    bits: &DependenceBits,
    left: WebVertex,
    right: WebVertex,
) -> WebRelation
{
    if bool::from(bits.contains(left, right)) {
        WebRelation::Precedes
    }
    else if bool::from(bits.contains(right, left)) {
        WebRelation::Follows
    }
    else {
        WebRelation::Independent
    }
}

/// A member's position inside the module being split.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Position(usize);

/// Which pairs a component search joins.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Joined
{
    /// Pairs one of which precedes the other.
    Comparable,
    /// Pairs neither of which precedes the other.
    Independent,
}

/// Whether a closure grew to the whole module it was grown inside.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Span
{
    /// Every member joined it.
    Whole,
    /// Some member stayed outside.
    Proper,
}

/// The decomposition under way: the tree built so far and the strong modules
/// still to split.
struct Builder<'bits>
{
    /// The order being decomposed.
    bits: &'bits DependenceBits,
    /// The nodes; a slot holds a placeholder event until its module is split.
    nodes: Vec<ModularNode>,
    /// Each node's parent and position.
    parents: Vec<(ModuleId, FactorIndex)>,
    /// Each node's number of ancestors.
    depths: Vec<ModuleCount>,
    /// Each vertex's leaf.
    leaves: Vec<ModuleId>,
    /// The strong modules still to split: a node and its vertices, ascending.
    work: Vec<(ModuleId, Vec<WebVertex>)>,
    /// One label per member of the module being split.
    labels: Vec<usize>,
    /// A search's frontier, as member positions.
    frontier: Vec<usize>,
}

impl<'bits> Builder<'bits>
{
    /// A builder whose one task is the whole order, at the root.
    ///
    /// # Specification
    /// - ensures: no task and no node for an empty order; otherwise one root
    ///   node and one task holding every vertex in ascending order.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the empty order builds no root and a chain's root
    ///   holds all its events.
    /// - witness: `tests::modular::the_empty_order_has_no_root`
    /// - witness: `tests::modular::a_chain_is_one_series_node`
    #[spec(ensures: |output| output.work.len() == usize::from(usize::from(count) != 0) && output.nodes.len() == output.work.len())]
    fn new(
        bits: &'bits DependenceBits,
        count: WebVertexCount,
    ) -> Self
    {
        let count = usize::from(count);
        let mut builder = Self {
            bits,
            nodes: Vec::new(),
            parents: Vec::new(),
            depths: Vec::new(),
            leaves: alloc::vec![ModuleId::default(); count],
            work: Vec::new(),
            labels: Vec::with_capacity(count),
            frontier: Vec::with_capacity(count),
        };
        if count != 0 {
            let root = ModuleId::from(0_usize);
            builder.nodes.push(ModularNode::Event(WebVertex::default()));
            builder.parents.push((root, FactorIndex::default()));
            builder.depths.push(ModuleCount::default());
            builder
                .work
                .push((root, (0 .. count).map(WebVertex::from).collect()));
        }
        builder
    }

    /// The finished tree.
    ///
    /// # Specification
    /// trivial.
    fn finish(self) -> ModularTree
    {
        ModularTree {
            nodes: self.nodes.into_boxed_slice(),
            parents: self.parents.into_boxed_slice(),
            depths: self.depths.into_boxed_slice(),
            leaves: self.leaves.into_boxed_slice(),
        }
    }

    /// Split one strong module into its node and its factors' tasks.
    ///
    /// # Specification
    /// - requires: `members` is a strong module of the order, ascending.
    /// - ensures: `slot` holds the module's event, or its parallel, series or
    ///   prime node, each factor a new node with its own task.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each of the three splits and the leaf are reached by
    ///   a named shape, and a generated order's tree reads back every pair.
    /// - witness: `tests::modular::series_and_parallel_alternate`
    /// - witness: `tests::modular::the_n_shape_is_prime`
    /// - witness: `tests::modular::the_tree_reads_back_the_order`
    #[spec(captures: before = self.nodes.len(), ensures: |()| self.nodes.len() >= before)]
    fn step(
        &mut self,
        slot: ModuleId,
        members: &[WebVertex],
    )
    {
        let node = if let &[only] = members {
            if let Some(leaf) = self.leaves.get_mut(usize::from(only)) {
                *leaf = slot;
            }
            ModularNode::Event(only)
        }
        else {
            let parts = self.components(members, Joined::Comparable);
            if parts.len() > 1 {
                ModularNode::Par(self.children(slot, parts))
            }
            else {
                let mut parts = self.components(members, Joined::Independent);
                if parts.len() > 1 {
                    let bits = self.bits;
                    parts.sort_by(|left, right| {
                        let (Some(&left), Some(&right)) = (left.first(), right.first())
                        else {
                            return Ordering::Equal;
                        };
                        match between(bits, left, right) {
                            WebRelation::Precedes => Ordering::Less,
                            WebRelation::Follows => Ordering::Greater,
                            WebRelation::Independent | WebRelation::Missing => Ordering::Equal,
                        }
                    });
                    ModularNode::Seq(self.children(slot, parts))
                }
                else {
                    self.prime(slot, members)
                }
            }
        };
        if let Some(held) = self.nodes.get_mut(usize::from(slot)) {
            *held = node;
        }
    }

    /// A prime node over `members`: its maximal proper modules as factors, and
    /// the precedence between them as the quotient.
    ///
    /// # Specification
    /// - requires: `members` is a strong module whose comparability and
    ///   incomparability graphs are both connected, ascending.
    /// - ensures: a [`ModularNode::Prime`] whose factors partition `members`,
    ///   in the order of their least vertex.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the N-shape's four events are four factors, twins
    ///   inside a prime shape are one factor, and every generated prime
    ///   quotient is prime.
    /// - witness: `tests::modular::the_n_shape_is_prime`
    /// - witness: `tests::modular::twins_fall_in_one_module`
    /// - witness: `tests::modular::the_tree_reads_back_the_order`
    #[spec(ensures: |output| matches!(output, ModularNode::Prime { ref factors, .. } if !factors.is_empty()))]
    fn prime(
        &mut self,
        slot: ModuleId,
        members: &[WebVertex],
    ) -> ModularNode
    {
        let unplaced = usize::MAX;
        let mut block_of = alloc::vec![unplaced; members.len()];
        let mut blocks: Vec<Vec<WebVertex>> = Vec::new();
        for (seed, &vertex) in members.iter().enumerate() {
            if block_of.get(seed).is_none_or(|&block| block != unplaced) {
                continue;
            }
            let index = blocks.len();
            if let Some(block) = block_of.get_mut(seed) {
                *block = index;
            }
            let mut block = alloc::vec![vertex];
            for (other, &joined) in members.iter().enumerate().skip(seed.saturating_add(1)) {
                if block_of.get(other).is_none_or(|&placed| placed != unplaced) {
                    continue;
                }
                if self.closure(members, Position(seed), Position(other)) == Span::Proper {
                    if let Some(placed) = block_of.get_mut(other) {
                        *placed = index;
                    }
                    block.push(joined);
                }
            }
            blocks.push(block);
        }
        let mut edges = Vec::new();
        for (earlier, first) in blocks.iter().enumerate() {
            for (later, second) in blocks.iter().enumerate() {
                if let (Some(&first), Some(&second)) = (first.first(), second.first())
                    && bool::from(self.bits.contains(first, second))
                {
                    edges.push((WebVertex::from(earlier), WebVertex::from(later)));
                }
            }
        }
        let quotient = DependenceBits::closure(WebVertexCount::from(blocks.len()), &edges);
        ModularNode::Prime {
            factors: self.children(slot, blocks),
            quotient,
        }
    }

    /// Whether the module `members[seed]` and `members[other]` generate inside
    /// `members` is the whole of it.
    ///
    /// # Specification
    /// - requires: `seed` and `other` are distinct positions of `members`.
    /// - ensures: [`Span::Whole`] exactly when every member joins the closure:
    ///   a member outside it joins whenever its relation to a member inside
    ///   differs from its relation to `members[seed]`.
    /// - panics: none.
    /// - intension: quadratic in `members.len()`: each member joins once and is
    ///   compared with every member outside.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — twins close to their pair inside a prime shape, and
    ///   every other pair of a prime shape closes to the whole.
    /// - witness: `tests::modular::twins_fall_in_one_module`
    /// - witness: `tests::modular::the_n_shape_is_prime`
    #[spec(requires: seed != other && seed.0 < members.len() && other.0 < members.len())]
    fn closure(
        &mut self,
        members: &[WebVertex],
        seed: Position,
        other: Position,
    ) -> Span
    {
        let (Position(seed), Position(other)) = (seed, other);
        let count = members.len();
        let (Some(&anchor), Some(_)) = (members.get(seed), members.get(other))
        else {
            return Span::Whole;
        };
        // `labels[z]` is one once `members[z]` is inside the closure or queued
        // to join it.
        self.labels.clear();
        self.labels.resize(count, 0);
        self.frontier.clear();
        let mut size = 0_usize;
        for joined in [seed, other] {
            if let Some(label) = self.labels.get_mut(joined) {
                *label = 1;
                size = size.saturating_add(1);
            }
        }
        self.frontier.push(other);
        while let Some(at) = self.frontier.pop() {
            if size >= count {
                return Span::Whole;
            }
            let Some(&inside) = members.get(at)
            else {
                continue;
            };
            for (outside, &vertex) in members.iter().enumerate() {
                if self.labels.get(outside).is_none_or(|&label| label != 0) {
                    continue;
                }
                if between(self.bits, vertex, inside) != between(self.bits, vertex, anchor) {
                    if let Some(label) = self.labels.get_mut(outside) {
                        *label = 1;
                    }
                    size = size.saturating_add(1);
                    self.frontier.push(outside);
                }
            }
        }
        if size >= count {
            Span::Whole
        }
        else {
            Span::Proper
        }
    }

    /// The components of `members` under the pairs `joined` names, each
    /// ascending, in the order of their least member.
    ///
    /// # Specification
    /// - ensures: a partition of `members` whose parts are the components of
    ///   the graph `joined` names over them.
    /// - panics: none.
    /// - intension: quadratic in `members.len()`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an antichain's members are each their own comparable
    ///   component, a chain's are each their own independent one, and an
    ///   alternation splits by the right graph at each level.
    /// - witness: `tests::modular::series_and_parallel_alternate`
    /// - witness: `tests::modular::the_tree_reads_back_the_order`
    #[spec(ensures: |output| output.iter().map(Vec::len).sum::<usize>() == members.len())]
    fn components(
        &mut self,
        members: &[WebVertex],
        joined: Joined,
    ) -> Vec<Vec<WebVertex>>
    {
        let unlabelled = usize::MAX;
        self.labels.clear();
        self.labels.resize(members.len(), unlabelled);
        let mut parts: Vec<Vec<WebVertex>> = Vec::new();
        for start in 0 .. members.len() {
            if self
                .labels
                .get(start)
                .is_none_or(|&label| label != unlabelled)
            {
                continue;
            }
            let part = parts.len();
            if let Some(label) = self.labels.get_mut(start) {
                *label = part;
            }
            self.frontier.clear();
            self.frontier.push(start);
            while let Some(at) = self.frontier.pop() {
                let Some(&from) = members.get(at)
                else {
                    continue;
                };
                for (next, &to) in members.iter().enumerate() {
                    if self
                        .labels
                        .get(next)
                        .is_none_or(|&label| label != unlabelled)
                    {
                        continue;
                    }
                    let linked = match (joined, between(self.bits, from, to)) {
                        (Joined::Comparable, WebRelation::Precedes | WebRelation::Follows)
                        | (Joined::Independent, WebRelation::Independent) => true,
                        (Joined::Comparable, WebRelation::Independent | WebRelation::Missing)
                        | (
                            Joined::Independent,
                            WebRelation::Precedes | WebRelation::Follows | WebRelation::Missing,
                        ) => false,
                    };
                    if linked {
                        if let Some(label) = self.labels.get_mut(next) {
                            *label = part;
                        }
                        self.frontier.push(next);
                    }
                }
            }
            parts.push(Vec::new());
        }
        for (position, &vertex) in members.iter().enumerate() {
            if let Some(part) = self
                .labels
                .get(position)
                .and_then(|&label| parts.get_mut(label))
            {
                part.push(vertex);
            }
        }
        parts
    }

    /// One node per part, each a factor of `parent` at its position, with its
    /// task queued.
    ///
    /// # Specification
    /// - ensures: one new node per part, in order, each recording `parent` and
    ///   its position.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every factor of a generated order's tree reads its
    ///   pairs back through its recorded parent and position.
    /// - witness: `tests::modular::the_tree_reads_back_the_order`
    #[spec(captures: [before = self.nodes.len(), count = parts.len()], ensures: |output| output.len() == count && self.nodes.len() == before.saturating_add(count))]
    fn children(
        &mut self,
        parent: ModuleId,
        parts: Vec<Vec<WebVertex>>,
    ) -> Box<[ModuleId]>
    {
        let depth = self
            .depths
            .get(usize::from(parent))
            .map_or(0, |&depth| usize::from(depth))
            .saturating_add(1);
        let mut factors = Vec::with_capacity(parts.len());
        for (position, part) in parts.into_iter().enumerate() {
            let id = ModuleId::from(self.nodes.len());
            self.nodes.push(ModularNode::Event(WebVertex::default()));
            self.parents.push((parent, FactorIndex::from(position)));
            self.depths.push(ModuleCount::from(depth));
            self.work.push((id, part));
            factors.push(id);
        }
        factors.into_boxed_slice()
    }
}
