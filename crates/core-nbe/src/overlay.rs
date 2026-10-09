//! The sharing overlay: sharing syntax over the core language, with no policy
//! in it.
//!
//! # Four families, four flat arenas
//!
//! An [`Overlay`] holds one vector per core family — values, computations,
//! value types and computation types — behind typed ids, so an id's type names
//! its family and its polarity. An overlay belongs to one run: nothing in it is
//! persisted, and teardown is four flat vector drops in any order.
//!
//! # A closed node set
//!
//! A node of every family is one of four kinds and nothing else:
//!
//! - **Opaque**: a node of the core arena the overlay is read against, held by
//!   id.
//! - **Bound**: one occurrence of a shared leg, named by how many shares lie
//!   between it and the share it belongs to and by which occurrence of that
//!   share it is.
//! - **Shared**: `body[x₀ … xₙ₋₁ ← leg]`, a body in which exactly `arity`
//!   occurrences stand for one leg. The leg may be of any family; the node is
//!   in its body's family.
//! - **Grafted**: one core former whose children are overlay nodes.
//!
//! Which part of a shared leg a duplication copies is the duplication
//! parameter's question, asked by the walk that duplicates. This module holds
//! the syntax the question is asked over and answers none of it.
//!
//! # Minting order is the acyclicity argument
//!
//! A node is minted only through its family's constructor, which refuses a
//! child that does not resolve. Every child was therefore minted before its
//! parent, and the reference graph is acyclic across all four families.
//!
//! # Validation is a worklist, and sharing is explicit or absent
//!
//! [`Overlay::validate`] walks a root in preorder over a heap task stack, with
//! one frame per share whose body it is inside, so depth costs heap rather than
//! host stack. A share's leg stands outside the share's own scope: an
//! occurrence inside a leg counts its distance from the shares enclosing the
//! share, never from the share itself.
//!
//! A node reached twice from one root is refused. Every node then has one
//! parent, so a walk enters each node once and costs the reachable overlay's
//! size; a node reused implicitly would cost its expansion, which is the cost
//! an explicit share exists to remove.
//!
//! # Erasure is total and takes no policy
//!
//! [`erase_value`] and its three siblings validate first, then mint the core
//! term a root stands for: each graft one core node after its children, each
//! opaque node as it stands, each share's leg once, and every occurrence that
//! one id. Indices are copied, never shifted, so an occurrence reads its
//! leg's free indices where it stands — the reading a core DAG gives a node
//! it reaches twice. The result is the unshared pipeline's input: no share
//! survives, and the pipeline walks each occurrence of the leg's id as a copy.
//! A refused erasure truncates the core arena back to where it found it.

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
use gandr_core_term::CoreArena;
use gandr_core_term::ValueId;
use gandr_core_term::ValueTypeId;
use gandr_core_term::Zone;
use gandr_kernel_strata::Level;
use gandr_kernel_term::BaseType;
use gandr_kernel_term::ConstantIndex;
use gandr_kernel_term::DeBruijnIndex;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Side;

/// The id of a [`ValueNode`] in an [`Overlay`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct OverlayValueId(u32);

/// The id of a [`CompNode`] in an [`Overlay`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct OverlayCompId(u32);

/// The id of a [`ValueTypeNode`] in an [`Overlay`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct OverlayValueTypeId(u32);

/// The id of a [`CompTypeNode`] in an [`Overlay`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct OverlayCompTypeId(u32);

/// The family an overlay node belongs to, which is the core family it stands
/// for.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum OverlayFamily
{
    /// Values.
    Value,
    /// Computations.
    Computation,
    /// Value types.
    ValueType,
    /// Computation types.
    CompType,
}

/// An overlay node of any family: what a share's leg and a refusal name.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum OverlayId
{
    /// A value node.
    Value(OverlayValueId),
    /// A computation node.
    Computation(OverlayCompId),
    /// A value-type node.
    ValueType(OverlayValueTypeId),
    /// A computation-type node.
    CompType(OverlayCompTypeId),
}

impl OverlayId
{
    /// The family this id names a node of.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn family(self) -> OverlayFamily
    {
        match self {
            | Self::Value(_) => OverlayFamily::Value,
            | Self::Computation(_) => OverlayFamily::Computation,
            | Self::ValueType(_) => OverlayFamily::ValueType,
            | Self::CompType(_) => OverlayFamily::CompType,
        }
    }
}

impl From<OverlayValueId> for OverlayId
{
    /// Name a value node as a node of any family.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(id: OverlayValueId) -> Self
    {
        Self::Value(id)
    }
}

impl From<OverlayCompId> for OverlayId
{
    /// Name a computation node as a node of any family.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(id: OverlayCompId) -> Self
    {
        Self::Computation(id)
    }
}

impl From<OverlayValueTypeId> for OverlayId
{
    /// Name a value-type node as a node of any family.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(id: OverlayValueTypeId) -> Self
    {
        Self::ValueType(id)
    }
}

impl From<OverlayCompTypeId> for OverlayId
{
    /// Name a computation-type node as a node of any family.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(id: OverlayCompTypeId) -> Self
    {
        Self::CompType(id)
    }
}

/// How many occurrences one share stands for.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ShareArity(u32);

impl From<u32> for ShareArity
{
    /// Read a `u32` as a share's arity.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(arity: u32) -> Self
    {
        Self(arity)
    }
}

impl From<ShareArity> for u32
{
    /// Read the arity back out as a `u32`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(arity: ShareArity) -> Self
    {
        arity.0
    }
}

/// How many shares lie between an occurrence and the share it belongs to: zero
/// names the innermost share whose body encloses the occurrence.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ShareDistance(u32);

impl From<u32> for ShareDistance
{
    /// Read a `u32` as an occurrence's distance.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(distance: u32) -> Self
    {
        Self(distance)
    }
}

impl From<ShareDistance> for u32
{
    /// Read the distance back out as a `u32`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(distance: ShareDistance) -> Self
    {
        distance.0
    }
}

/// Which occurrence of its share an occurrence is, counted from zero in the
/// preorder of the share's body.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SharePosition(u32);

impl From<u32> for SharePosition
{
    /// Read a `u32` as an occurrence's position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: u32) -> Self
    {
        Self(position)
    }
}

impl From<SharePosition> for u32
{
    /// Read the position back out as a `u32`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: SharePosition) -> Self
    {
        position.0
    }
}

/// One occurrence of a shared leg.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Bound
{
    /// The shares between this occurrence and the one it belongs to.
    pub distance: ShareDistance,
    /// Which occurrence of that share this is.
    pub position: SharePosition,
}

/// `body[x₀ … xₙ₋₁ ← leg]`: a body in which exactly `arity` occurrences stand
/// for one leg.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Sharing<Body>
{
    /// How many occurrences the body holds for this share.
    pub arity: ShareArity,
    /// The shared leg, of any family, standing outside this share's scope.
    pub leg: OverlayId,
    /// The body, in this node's own family.
    pub body: Body,
}

impl<Body> Sharing<Body>
where
    Body: Into<OverlayId>,
{
    /// The same share with its body named as a node of any family.
    ///
    /// # Specification
    /// trivial.
    fn widened(self) -> Sharing<OverlayId>
    {
        Sharing {
            arity: self.arity,
            leg: self.leg,
            body: self.body.into(),
        }
    }
}

/// A value-family overlay node.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ValueNode
{
    /// A core value, held by id.
    Opaque(ValueId),
    /// One occurrence of a value leg.
    Bound(Bound),
    /// A value body sharing one leg among its occurrences.
    Shared(Sharing<OverlayValueId>),
    /// One core value former over overlay children.
    Grafted(ValueGraft),
}

/// A computation-family overlay node.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum CompNode
{
    /// A core computation, held by id.
    Opaque(ComputationId),
    /// One occurrence of a computation leg.
    Bound(Bound),
    /// A computation body sharing one leg among its occurrences.
    Shared(Sharing<OverlayCompId>),
    /// One core computation former over overlay children.
    Grafted(CompGraft),
}

/// A value-type-family overlay node.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ValueTypeNode
{
    /// A core value type, held by id.
    Opaque(ValueTypeId),
    /// One occurrence of a value-type leg.
    Bound(Bound),
    /// A value-type body sharing one leg among its occurrences.
    Shared(Sharing<OverlayValueTypeId>),
    /// One core value-type former over overlay children.
    Grafted(ValueTypeGraft),
}

/// A computation-type-family overlay node.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum CompTypeNode
{
    /// A core computation type, held by id.
    Opaque(CompTypeId),
    /// One occurrence of a computation-type leg.
    Bound(Bound),
    /// A computation-type body sharing one leg among its occurrences.
    Shared(Sharing<OverlayCompTypeId>),
    /// One core computation-type former over overlay children.
    Grafted(CompTypeGraft),
}

/// A core value former whose children are overlay nodes, one arm per former of
/// [`gandr_core_term::Value`].
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ValueGraft
{
    /// A bound variable of the core language, counted in its zone.
    Variable
    {
        /// The zone the index counts in.
        zone: Zone,
        /// The de Bruijn index within that zone.
        index: DeBruijnIndex,
    },
    /// A reference to a prior declaration.
    Constant(ConstantIndex),
    /// The unit value.
    Unit,
    /// A base-type literal.
    Literal(Literal),
    /// A pair.
    Pair(OverlayValueId, OverlayValueId),
    /// A sum injection on the given side.
    Injection(Side, OverlayValueId),
    /// A thunk over a computation.
    Thunk(OverlayCompId),
    /// An explicit universe lift.
    Lift
    {
        /// The target level.
        target: Level,
        /// The value lifted.
        body: OverlayValueId,
    },
}

/// A core computation former whose children are overlay nodes, one arm per
/// former of [`gandr_core_term::Computation`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CompGraft
{
    /// A lambda over its body.
    Lambda(OverlayCompId),
    /// A computation applied to a value.
    Application(OverlayCompId, OverlayValueId),
    /// A returner.
    Return(OverlayValueId),
    /// A sequencing bind of a computation into a body.
    Bind(OverlayCompId, OverlayCompId),
    /// A force of a thunk value.
    Force(OverlayValueId),
    /// A sum elimination.
    Case
    {
        /// The scrutinee.
        scrutinee: OverlayValueId,
        /// The left branch.
        on_left: OverlayCompId,
        /// The right branch.
        on_right: OverlayCompId,
    },
}

/// A core value-type former whose children are overlay nodes, one arm per
/// former of [`gandr_core_term::ValueType`].
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ValueTypeGraft
{
    /// A rigid base-type atom.
    Base(BaseType),
    /// The unit type.
    Unit,
    /// The non-dependent product.
    Product(OverlayValueTypeId, OverlayValueTypeId),
    /// The sum.
    Sum(OverlayValueTypeId, OverlayValueTypeId),
    /// The thunk type of a computation type.
    Thunk(OverlayCompTypeId),
    /// The universe at a level.
    Universe(Level),
    /// An explicit lift of a value type.
    Lift
    {
        /// The value type lifted.
        inner: OverlayValueTypeId,
        /// The target level.
        target: Level,
    },
    /// The type a code denotes.
    Element
    {
        /// The code.
        code: OverlayValueId,
        /// The universe the code is read out of.
        target: Level,
    },
    /// A sealed abstract type.
    Abstract(ConstantIndex),
}

/// A core computation-type former whose children are overlay nodes, one arm
/// per former of [`gandr_core_term::CompType`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CompTypeGraft
{
    /// The returner of a value type.
    Returner(OverlayValueTypeId),
    /// The non-dependent function type.
    Arrow
    {
        /// The value-type domain.
        domain: OverlayValueTypeId,
        /// The codomain, in the ambient context.
        codomain: OverlayCompTypeId,
    },
    /// The dependent function type.
    Pi
    {
        /// The value-type domain.
        domain: OverlayValueTypeId,
        /// The codomain, under the domain's binder.
        codomain: OverlayCompTypeId,
    },
}

/// Why a node could not be minted.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum OverlayFault
{
    /// A child names no node of its family in this overlay.
    DanglingChild
    {
        /// The child that does not resolve.
        child: OverlayId,
    },
    /// The family already holds as many nodes as an id can name.
    FamilyFull
    {
        /// The family that is full.
        family: OverlayFamily,
    },
}

/// Why an overlay was refused, named at the node where the walk met it.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum OverlayRefusal
{
    /// A reached id names no node of this overlay.
    Unresolved
    {
        /// The id that does not resolve.
        node: OverlayId,
    },
    /// A node was reached a second time: sharing that no share names.
    ReachedTwice
    {
        /// The node reached twice.
        node: OverlayId,
    },
    /// An occurrence counts out past every share whose body encloses it, so
    /// the node set is open.
    OpenReference
    {
        /// The occurrence.
        node: OverlayId,
    },
    /// An occurrence stands in another family than its share's leg.
    FamilyMismatch
    {
        /// The occurrence.
        node: OverlayId,
        /// The occurrence's family.
        occurrence: OverlayFamily,
        /// The leg's family.
        leg: OverlayFamily,
    },
    /// An occurrence's position is not the next one in its share's preorder.
    PositionOutOfOrder
    {
        /// The occurrence.
        node: OverlayId,
        /// The position the preorder reached.
        expected: SharePosition,
        /// The position the occurrence names.
        found: SharePosition,
    },
    /// An occurrence of a share that already holds its arity.
    SurplusOccurrence
    {
        /// The occurrence.
        node: OverlayId,
        /// The share's arity.
        arity: ShareArity,
    },
    /// A share whose body held fewer occurrences than its arity.
    MissingOccurrences
    {
        /// The share.
        share: OverlayId,
        /// The share's arity.
        arity: ShareArity,
        /// The first position no occurrence took.
        next: SharePosition,
    },
    /// A share standing for no occurrence.
    ZeroArity
    {
        /// The share.
        share: OverlayId,
    },
    /// The walk closed a share it had not opened. Unreachable while every close
    /// is pushed beneath the open it pairs with; kept so the walk fails closed
    /// rather than answering.
    MachineInvariant,
}

/// A snapshot of the four family lengths.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct OverlayWatermark
{
    /// The value family length.
    values: usize,
    /// The computation family length.
    computations: usize,
    /// The value-type family length.
    value_types: usize,
    /// The computation-type family length.
    comp_types: usize,
}

/// The per-run arena of sharing syntax over one core arena.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Overlay
{
    /// The value nodes, in minting order.
    values: Vec<ValueNode>,
    /// The computation nodes.
    computations: Vec<CompNode>,
    /// The value-type nodes.
    value_types: Vec<ValueTypeNode>,
    /// The computation-type nodes.
    comp_types: Vec<CompTypeNode>,
}

impl Overlay
{
    /// An empty overlay.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn new() -> Self
    {
        Self::default()
    }

    /// The current watermark: the four family lengths.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each component equals the current length of the family it
    ///   names, so the mark is an exact snapshot of this overlay at this call.
    /// - provides: the mark [`Overlay::truncate_to`] discards later nodes back
    ///   to.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn watermark(&self) -> OverlayWatermark
    {
        OverlayWatermark {
            values: self.values.len(),
            computations: self.computations.len(),
            value_types: self.value_types.len(),
            comp_types: self.comp_types.len(),
        }
    }

    /// Truncate every family back to `watermark`, dropping later nodes.
    ///
    /// # Specification
    /// - requires: `watermark` was taken from this overlay and no family has
    ///   since shrunk below it.
    /// - ensures: each family holds exactly its watermark-many leading nodes,
    ///   and a lookup of an id minted after the mark fails closed.
    /// - provides: the discard of a speculative overlay and, at the default
    ///   watermark, the run's whole teardown as four flat vector drops in any
    ///   order. Every node a retained node names was minted before it, so a
    ///   mark from this overlay leaves no retained node naming a dropped one.
    /// - fails: never — a truncation past the end is a no-op.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — one decision surface per family, separated by a mark
    ///   below the current length and the floor, with a dropped id asserted
    ///   unresolved and a retained one asserted resolved.
    /// - witness: `overlay::tests::truncating_to_a_watermark_drops_later_nodes`
    /// - witness:
    ///   `teardown::teardown::a_deep_overlay_validates_and_is_released_in_both_orders_inside_a_small_stack`
    #[inline]
    #[spec(
        captures: entry_mark = self.watermark(),
        ensures: self.values.len() == watermark.values.min(entry_mark.values)
            && self.computations.len() == watermark.computations.min(entry_mark.computations)
            && self.value_types.len() == watermark.value_types.min(entry_mark.value_types)
            && self.comp_types.len() == watermark.comp_types.min(entry_mark.comp_types),
    )]
    pub fn truncate_to(
        &mut self,
        watermark: OverlayWatermark,
    )
    {
        self.values.truncate(watermark.values);
        self.computations.truncate(watermark.computations);
        self.value_types.truncate(watermark.value_types);
        self.comp_types.truncate(watermark.comp_types);
    }

    /// Resolve a value node, or `None` when the id dangles.
    ///
    /// # Specification
    /// - requires: nothing — an id from another overlay is admissible input.
    /// - ensures: the node this overlay holds for `id`, for every id below the
    ///   family length.
    /// - provides: the checked read every walk resolves a value node through.
    /// - fails: yields nothing at or above the family length; an id carries no
    ///   overlay provenance, so an in-range foreign id resolves here.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn value(
        &self,
        id: OverlayValueId,
    ) -> Option<&ValueNode>
    {
        self.values.get(offset(Index(id.0)).0)
    }

    /// Resolve a computation node, or `None` when the id dangles.
    ///
    /// # Specification
    /// - requires: nothing — an id from another overlay is admissible input.
    /// - ensures: the node this overlay holds for `id`, for every id below the
    ///   family length.
    /// - provides: the checked read every walk resolves a computation node
    ///   through.
    /// - fails: yields nothing at or above the family length; an in-range
    ///   foreign id resolves here.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn computation(
        &self,
        id: OverlayCompId,
    ) -> Option<&CompNode>
    {
        self.computations.get(offset(Index(id.0)).0)
    }

    /// Resolve a value-type node, or `None` when the id dangles.
    ///
    /// # Specification
    /// - requires: nothing — an id from another overlay is admissible input.
    /// - ensures: the node this overlay holds for `id`, for every id below the
    ///   family length.
    /// - provides: the checked read every walk resolves a value-type node
    ///   through.
    /// - fails: yields nothing at or above the family length; an in-range
    ///   foreign id resolves here.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn value_type(
        &self,
        id: OverlayValueTypeId,
    ) -> Option<&ValueTypeNode>
    {
        self.value_types.get(offset(Index(id.0)).0)
    }

    /// Resolve a computation-type node, or `None` when the id dangles.
    ///
    /// # Specification
    /// - requires: nothing — an id from another overlay is admissible input.
    /// - ensures: the node this overlay holds for `id`, for every id below the
    ///   family length.
    /// - provides: the checked read every walk resolves a computation-type node
    ///   through.
    /// - fails: yields nothing at or above the family length; an in-range
    ///   foreign id resolves here.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn comp_type(
        &self,
        id: OverlayCompTypeId,
    ) -> Option<&CompTypeNode>
    {
        self.comp_types.get(offset(Index(id.0)).0)
    }

    /// Mint a value node.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the node is held at the returned id, one past the
    ///   family's previous last; on refusal nothing is minted.
    /// - provides: the only way a value node enters the overlay, so every child
    ///   a value node names was minted before it.
    /// - fails: [`OverlayFault::DanglingChild`] naming the first child, leg
    ///   before body and left to right, that does not resolve, and
    ///   [`OverlayFault::FamilyFull`] when the family holds as many nodes as an
    ///   id can name.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`OverlayFault::DanglingChild`] — a child does not resolve.
    /// - [`OverlayFault::FamilyFull`] — no id is left to mint.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are the child check and the
    ///   family ceiling, separated by a node whose children resolve, a graft
    ///   and a share each naming a child from another overlay, and the family
    ///   length asserted unchanged after a refusal; the ceiling needs four
    ///   billion nodes and stays prose.
    /// - witness: `overlay::tests::minting_refuses_a_child_the_overlay_does_not_hold`
    #[inline]
    pub fn mint_value(
        &mut self,
        node: ValueNode,
    ) -> Result<OverlayValueId, OverlayFault>
    {
        node.shape().children().held_in(self)?;
        let index = next_index(Offset(self.values.len()), OverlayFamily::Value)?;
        self.values.push(node);
        Ok(OverlayValueId(index.0))
    }

    /// Mint a computation node.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the node is held at the returned id, one past the
    ///   family's previous last; on refusal nothing is minted.
    /// - provides: the only way a computation node enters the overlay.
    /// - fails: [`OverlayFault::DanglingChild`] naming the first child that
    ///   does not resolve, and [`OverlayFault::FamilyFull`] at the id ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`OverlayFault::DanglingChild`] — a child does not resolve.
    /// - [`OverlayFault::FamilyFull`] — no id is left to mint.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are the child check and the
    ///   family ceiling, separated by a share whose leg is from another overlay
    ///   and its successful mint once the leg resolves.
    /// - witness: `overlay::tests::minting_refuses_a_child_the_overlay_does_not_hold`
    #[inline]
    pub fn mint_computation(
        &mut self,
        node: CompNode,
    ) -> Result<OverlayCompId, OverlayFault>
    {
        node.shape().children().held_in(self)?;
        let index = next_index(Offset(self.computations.len()), OverlayFamily::Computation)?;
        self.computations.push(node);
        Ok(OverlayCompId(index.0))
    }

    /// Mint a value-type node.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the node is held at the returned id, one past the
    ///   family's previous last; on refusal nothing is minted.
    /// - provides: the only way a value-type node enters the overlay.
    /// - fails: [`OverlayFault::DanglingChild`] naming the first child that
    ///   does not resolve, and [`OverlayFault::FamilyFull`] at the id ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`OverlayFault::DanglingChild`] — a child does not resolve.
    /// - [`OverlayFault::FamilyFull`] — no id is left to mint.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are the child check and the
    ///   family ceiling, separated by a code from another overlay refused and a
    ///   lift chain minted.
    /// - witness: `overlay::tests::minting_refuses_a_child_the_overlay_does_not_hold`
    /// - witness:
    ///   `teardown::teardown::a_deep_overlay_validates_and_is_released_in_both_orders_inside_a_small_stack`
    #[inline]
    pub fn mint_value_type(
        &mut self,
        node: ValueTypeNode,
    ) -> Result<OverlayValueTypeId, OverlayFault>
    {
        node.shape().children().held_in(self)?;
        let index = next_index(Offset(self.value_types.len()), OverlayFamily::ValueType)?;
        self.value_types.push(node);
        Ok(OverlayValueTypeId(index.0))
    }

    /// Mint a computation-type node.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the node is held at the returned id, one past the
    ///   family's previous last; on refusal nothing is minted.
    /// - provides: the only way a computation-type node enters the overlay.
    /// - fails: [`OverlayFault::DanglingChild`] naming the first child that
    ///   does not resolve, and [`OverlayFault::FamilyFull`] at the id ceiling.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`OverlayFault::DanglingChild`] — a child does not resolve.
    /// - [`OverlayFault::FamilyFull`] — no id is left to mint.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are the child check and the
    ///   family ceiling, separated by an arrow whose codomain is from another
    ///   overlay refused and the same arrow minted over its own codomain.
    /// - witness: `overlay::tests::minting_refuses_a_child_the_overlay_does_not_hold`
    #[inline]
    pub fn mint_comp_type(
        &mut self,
        node: CompTypeNode,
    ) -> Result<OverlayCompTypeId, OverlayFault>
    {
        node.shape().children().held_in(self)?;
        let index = next_index(Offset(self.comp_types.len()), OverlayFamily::CompType)?;
        self.comp_types.push(node);
        Ok(OverlayCompTypeId(index.0))
    }

    /// Validate the overlay reachable from `root`.
    ///
    /// # Specification
    /// - requires: nothing — a root from another overlay, and one minted after
    ///   a truncation, are admissible input.
    /// - ensures: `Ok` exactly when every node reachable from `root` resolves
    ///   and is reached once; every occurrence names a share whose body
    ///   encloses it, whose leg is of the occurrence's family, at that share's
    ///   next preorder position and below its arity; and every share has a
    ///   non-zero arity its body's occurrences reach exactly.
    /// - provides: the closed, tree-shaped overlay a walk over it is total on.
    /// - fails: the first violation in preorder, named by its variant and the
    ///   node it stands at.
    /// - panics: none.
    /// - intension: one task per node and two more per share, all on the heap;
    ///   each node is entered once, so the walk costs the reachable overlay's
    ///   size.
    ///
    /// # Errors
    /// - [`OverlayRefusal::Unresolved`] — a reached id names no node.
    /// - [`OverlayRefusal::ReachedTwice`] — a node is reached a second time.
    /// - [`OverlayRefusal::OpenReference`] — an occurrence counts out past
    ///   every enclosing share.
    /// - [`OverlayRefusal::FamilyMismatch`] — an occurrence and its leg differ
    ///   in family.
    /// - [`OverlayRefusal::PositionOutOfOrder`] — an occurrence skips or
    ///   repeats a position.
    /// - [`OverlayRefusal::SurplusOccurrence`] — a share holds more occurrences
    ///   than its arity.
    /// - [`OverlayRefusal::MissingOccurrences`] — a share holds fewer.
    /// - [`OverlayRefusal::ZeroArity`] — a share stands for nothing.
    /// - [`OverlayRefusal::MachineInvariant`] — the walk's own pairing broke.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the decision surfaces are the resolution and reuse
    ///   checks, the occurrence rules and the share rules, separated by one
    ///   refusal per reachable variant asserted with the node it names, by the
    ///   explicit share that accepts what implicit reuse refuses, and by nested
    ///   shares whose leg and body count distance from different frames; the
    ///   walk's depth is separated from the host stack by a chain validated
    ///   inside a small stack.
    /// - witness: `overlay::tests::validation_refuses_an_open_node_set_by_name`
    /// - witness: `overlay::tests::validation_refuses_an_occurrence_of_another_family`
    /// - witness: `overlay::tests::validation_holds_each_share_to_its_arity_in_preorder`
    /// - witness: `overlay::tests::validation_refuses_a_node_reached_twice`
    /// - witness: `overlay::tests::validation_refuses_a_root_the_overlay_does_not_hold`
    /// - witness: `overlay::tests::a_leg_counts_from_outside_its_share`
    /// - witness:
    ///   `teardown::teardown::a_deep_overlay_validates_and_is_released_in_both_orders_inside_a_small_stack`
    #[inline]
    pub fn validate(
        &self,
        root: OverlayId,
    ) -> Result<(), OverlayRefusal>
    {
        // economy: the reached set grows with the walk rather than with the
        // overlay, so validating one small root of a large overlay costs that
        // root's size; its log factor is the price of not sizing a table to
        // every family.
        let mut reached = BTreeSet::new();
        let mut tasks = Vec::from([Check::Enter(root)]);
        let mut frames: Vec<Frame> = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                | Check::Enter(node) => {
                    let shape = self.shape(node)?;
                    if !reached.insert(node) {
                        return Err(OverlayRefusal::ReachedTwice { node });
                    }
                    match shape {
                        | Shape::Opaque(_) => {},
                        | Shape::Bound(bound) => {
                            occur(&mut frames, node, bound)?;
                        },
                        | Shape::Shared(sharing) => {
                            if sharing.arity == ShareArity(0) {
                                return Err(OverlayRefusal::ZeroArity { share: node });
                            }
                            tasks.push(Check::Close { share: node });
                            tasks.push(Check::Enter(sharing.body));
                            tasks.push(Check::Open(Frame {
                                arity: sharing.arity,
                                leg: sharing.leg.family(),
                                next: SharePosition(0),
                            }));
                            tasks.push(Check::Enter(sharing.leg));
                        },
                        | Shape::Grafted(children) => {
                            children.push_reversed(&mut tasks, Check::Enter);
                        },
                    }
                },
                | Check::Open(frame) => frames.push(frame),
                | Check::Close { share } => {
                    let Some(frame) = frames.pop()
                    else {
                        return Err(OverlayRefusal::MachineInvariant);
                    };
                    if frame.next.0 != frame.arity.0 {
                        return Err(OverlayRefusal::MissingOccurrences {
                            share,
                            arity: frame.arity,
                            next: frame.next,
                        });
                    }
                },
            }
        }
        Ok(())
    }

    /// Resolve any node to its shape.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the shape of the node `node` names.
    /// - provides: the one family dispatch validation reads every node through.
    /// - fails: [`OverlayRefusal::Unresolved`] when `node` names no node.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`OverlayRefusal::Unresolved`] — `node` names no node.
    fn shape(
        &self,
        node: OverlayId,
    ) -> Result<Shape, OverlayRefusal>
    {
        let shape = match node {
            | OverlayId::Value(id) => self.value(id).map(ValueNode::shape),
            | OverlayId::Computation(id) => self.computation(id).map(CompNode::shape),
            | OverlayId::ValueType(id) => self.value_type(id).map(ValueTypeNode::shape),
            | OverlayId::CompType(id) => self.comp_type(id).map(CompTypeNode::shape),
        };
        shape.ok_or(OverlayRefusal::Unresolved { node })
    }

    /// Check that a child resolves.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Ok` exactly when `child` names a node of this overlay.
    /// - provides: the dangling check every mint runs on every child.
    /// - fails: [`OverlayFault::DanglingChild`] naming `child`.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`OverlayFault::DanglingChild`] — `child` names no node.
    fn held(
        &self,
        child: OverlayId,
    ) -> Result<(), OverlayFault>
    {
        let present = match child {
            | OverlayId::Value(id) => self.value(id).is_some(),
            | OverlayId::Computation(id) => self.computation(id).is_some(),
            | OverlayId::ValueType(id) => self.value_type(id).is_some(),
            | OverlayId::CompType(id) => self.comp_type(id).is_some(),
        };
        if present {
            Ok(())
        }
        else {
            Err(OverlayFault::DanglingChild { child })
        }
    }
}

/// The offset an overlay id reads its family vector at.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Offset(usize);

/// The stored index of one node within its family.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Index(u32);

/// Narrow an id's index to the offset a checked vector read takes.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the equal offset, lossless on every supported platform of at
///   least 32 bits.
/// - provides: the total, panic-free index-to-offset narrowing.
/// - fails: never; it saturates at the offset ceiling, which a checked read
///   then rejects.
/// - panics: none.
#[spec(ensures: |ret| u32::try_from(ret.0).is_ok_and(|narrowed| narrowed == index.0)
    || ret.0 == usize::MAX)]
fn offset(index: Index) -> Offset
{
    Offset(usize::try_from(index.0).unwrap_or(usize::MAX))
}

/// The index the next node of a family of `length` nodes takes.
///
/// # Specification
/// - requires: `length` is the current length of `family`.
/// - ensures: the equal index when it fits an id.
/// - provides: the mint-time ceiling, refused rather than saturated, so two
///   nodes never share an id.
/// - fails: [`OverlayFault::FamilyFull`] when `length` does not fit an id.
/// - panics: none.
///
/// # Errors
/// - [`OverlayFault::FamilyFull`] — no id is left in `family`.
fn next_index(
    length: Offset,
    family: OverlayFamily,
) -> Result<Index, OverlayFault>
{
    u32::try_from(length.0)
        .map(Index)
        .map_err(|_overflow| OverlayFault::FamilyFull { family })
}

/// The children of one node, left to right, with no allocation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Children
{
    /// A leaf.
    Leaf,
    /// One child.
    One(OverlayId),
    /// Two children.
    Two(OverlayId, OverlayId),
    /// Three children.
    Three(OverlayId, OverlayId, OverlayId),
}

impl Children
{
    /// Check that every child resolves in `overlay`, left to right.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Ok` exactly when every child resolves.
    /// - provides: the mint-time dangling check, naming the first child that
    ///   fails.
    /// - fails: [`OverlayFault::DanglingChild`] naming that child.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`OverlayFault::DanglingChild`] — a child does not resolve.
    fn held_in(
        self,
        overlay: &Overlay,
    ) -> Result<(), OverlayFault>
    {
        match self {
            | Self::Leaf => {},
            | Self::One(only) => {
                overlay.held(only)?;
            },
            | Self::Two(first, second) => {
                overlay.held(first)?;
                overlay.held(second)?;
            },
            | Self::Three(first, second, third) => {
                overlay.held(first)?;
                overlay.held(second)?;
                overlay.held(third)?;
            },
        }
        Ok(())
    }

    /// Push one task per child, rightmost first, so the leftmost child runs
    /// first off the stack.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the tasks are pushed in reverse child order.
    /// - provides: the left-to-right traversal order every walk shares, which
    ///   is the preorder an occurrence's position counts in.
    /// - fails: never.
    /// - panics: none.
    fn push_reversed<Task>(
        self,
        tasks: &mut Vec<Task>,
        enter: fn(OverlayId) -> Task,
    )
    {
        match self {
            | Self::Leaf => {},
            | Self::One(only) => tasks.push(enter(only)),
            | Self::Two(first, second) => {
                tasks.push(enter(second));
                tasks.push(enter(first));
            },
            | Self::Three(first, second, third) => {
                tasks.push(enter(third));
                tasks.push(enter(second));
                tasks.push(enter(first));
            },
        }
    }
}

/// A node's kind, with what a walk needs of it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Shape
{
    /// An opaque core node, by its core id.
    Opaque(CoreId),
    /// An occurrence.
    Bound(Bound),
    /// A share, its body named as a node of any family.
    Shared(Sharing<OverlayId>),
    /// A graft over these children.
    Grafted(Children),
}

impl Shape
{
    /// The ids this node names: leg then body for a share, the graft's children
    /// for a graft, nothing for a leaf.
    ///
    /// # Specification
    /// trivial.
    fn children(self) -> Children
    {
        match self {
            | Self::Opaque(_) | Self::Bound(_) => Children::Leaf,
            | Self::Shared(sharing) => Children::Two(sharing.leg, sharing.body),
            | Self::Grafted(children) => children,
        }
    }
}

impl ValueNode
{
    /// This node's shape.
    ///
    /// # Specification
    /// trivial.
    fn shape(&self) -> Shape
    {
        match *self {
            | Self::Opaque(id) => Shape::Opaque(CoreId::Value(id)),
            | Self::Bound(bound) => Shape::Bound(bound),
            | Self::Shared(sharing) => Shape::Shared(sharing.widened()),
            | Self::Grafted(ref graft) => Shape::Grafted(graft.children()),
        }
    }
}

impl CompNode
{
    /// This node's shape.
    ///
    /// # Specification
    /// trivial.
    fn shape(&self) -> Shape
    {
        match *self {
            | Self::Opaque(id) => Shape::Opaque(CoreId::Computation(id)),
            | Self::Bound(bound) => Shape::Bound(bound),
            | Self::Shared(sharing) => Shape::Shared(sharing.widened()),
            | Self::Grafted(graft) => Shape::Grafted(graft.children()),
        }
    }
}

impl ValueTypeNode
{
    /// This node's shape.
    ///
    /// # Specification
    /// trivial.
    fn shape(&self) -> Shape
    {
        match *self {
            | Self::Opaque(id) => Shape::Opaque(CoreId::ValueType(id)),
            | Self::Bound(bound) => Shape::Bound(bound),
            | Self::Shared(sharing) => Shape::Shared(sharing.widened()),
            | Self::Grafted(ref graft) => Shape::Grafted(graft.children()),
        }
    }
}

impl CompTypeNode
{
    /// This node's shape.
    ///
    /// # Specification
    /// trivial.
    fn shape(&self) -> Shape
    {
        match *self {
            | Self::Opaque(id) => Shape::Opaque(CoreId::CompType(id)),
            | Self::Bound(bound) => Shape::Bound(bound),
            | Self::Shared(sharing) => Shape::Shared(sharing.widened()),
            | Self::Grafted(graft) => Shape::Grafted(graft.children()),
        }
    }
}

impl ValueGraft
{
    /// The graft's children, left to right as the core former orders them.
    ///
    /// # Specification
    /// trivial.
    fn children(&self) -> Children
    {
        match *self {
            | Self::Variable { .. } | Self::Constant(_) | Self::Unit | Self::Literal(_) => {
                Children::Leaf
            },
            | Self::Pair(first, second) => {
                Children::Two(OverlayId::Value(first), OverlayId::Value(second))
            },
            | Self::Injection(_, body) | Self::Lift { body, .. } => {
                Children::One(OverlayId::Value(body))
            },
            | Self::Thunk(body) => Children::One(OverlayId::Computation(body)),
        }
    }
}

impl CompGraft
{
    /// The graft's children, left to right as the core former orders them.
    ///
    /// # Specification
    /// trivial.
    fn children(self) -> Children
    {
        match self {
            | Self::Lambda(body) => Children::One(OverlayId::Computation(body)),
            | Self::Application(head, argument) => {
                Children::Two(OverlayId::Computation(head), OverlayId::Value(argument))
            },
            | Self::Return(value) | Self::Force(value) => Children::One(OverlayId::Value(value)),
            | Self::Bind(bound, body) => {
                Children::Two(OverlayId::Computation(bound), OverlayId::Computation(body))
            },
            | Self::Case {
                scrutinee,
                on_left,
                on_right,
            } => Children::Three(
                OverlayId::Value(scrutinee),
                OverlayId::Computation(on_left),
                OverlayId::Computation(on_right),
            ),
        }
    }
}

impl ValueTypeGraft
{
    /// The graft's children, left to right as the core former orders them.
    ///
    /// # Specification
    /// trivial.
    fn children(&self) -> Children
    {
        match *self {
            | Self::Base(_) | Self::Unit | Self::Universe(_) | Self::Abstract(_) => Children::Leaf,
            | Self::Product(first, second) | Self::Sum(first, second) => {
                Children::Two(OverlayId::ValueType(first), OverlayId::ValueType(second))
            },
            | Self::Thunk(body) => Children::One(OverlayId::CompType(body)),
            | Self::Lift { inner, .. } => Children::One(OverlayId::ValueType(inner)),
            | Self::Element { code, .. } => Children::One(OverlayId::Value(code)),
        }
    }
}

impl CompTypeGraft
{
    /// The graft's children, left to right as the core former orders them.
    ///
    /// # Specification
    /// trivial.
    fn children(self) -> Children
    {
        match self {
            | Self::Returner(result) => Children::One(OverlayId::ValueType(result)),
            | Self::Arrow { domain, codomain } | Self::Pi { domain, codomain } => {
                Children::Two(OverlayId::ValueType(domain), OverlayId::CompType(codomain))
            },
        }
    }
}

/// One share whose body the validation walk is inside.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Frame
{
    /// The share's arity.
    arity: ShareArity,
    /// The family of the share's leg.
    leg: OverlayFamily,
    /// The position the next occurrence must name.
    next: SharePosition,
}

/// One pending step of the validation walk.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Check
{
    /// Check one node and queue its children.
    Enter(OverlayId),
    /// Open a share's scope, before its body.
    Open(Frame),
    /// Close the innermost scope, after the body of `share`.
    Close
    {
        /// The share whose scope closes.
        share: OverlayId,
    },
}

/// Check one occurrence against the frames open around it, and take its
/// position.
///
/// # Specification
/// - requires: `frames` holds one frame per share whose body encloses `node`,
///   innermost last.
/// - ensures: on success the named frame's next position has advanced by one.
/// - provides: the four occurrence rules, in the order a refusal names them:
///   the reference closes, the families agree, the share has room, and the
///   position is the next one.
/// - fails: [`OverlayRefusal::OpenReference`],
///   [`OverlayRefusal::FamilyMismatch`], [`OverlayRefusal::SurplusOccurrence`]
///   or [`OverlayRefusal::PositionOutOfOrder`], each naming `node`.
/// - panics: none.
///
/// # Errors
/// - [`OverlayRefusal::OpenReference`] — the distance counts past every frame.
/// - [`OverlayRefusal::FamilyMismatch`] — the leg is of another family.
/// - [`OverlayRefusal::SurplusOccurrence`] — the share already holds its arity.
/// - [`OverlayRefusal::PositionOutOfOrder`] — the position is not the next.
fn occur(
    frames: &mut [Frame],
    node: OverlayId,
    bound: Bound,
) -> Result<(), OverlayRefusal>
{
    let distance = usize::try_from(bound.distance.0).unwrap_or(usize::MAX);
    let Some(frame) = frames
        .len()
        .checked_sub(1)
        .and_then(|innermost| innermost.checked_sub(distance))
        .and_then(|named| frames.get_mut(named))
    else {
        return Err(OverlayRefusal::OpenReference { node });
    };
    if frame.leg != node.family() {
        return Err(OverlayRefusal::FamilyMismatch {
            node,
            occurrence: node.family(),
            leg: frame.leg,
        });
    }
    if frame.next.0 >= frame.arity.0 {
        return Err(OverlayRefusal::SurplusOccurrence {
            node,
            arity: frame.arity,
        });
    }
    if bound.position != frame.next {
        return Err(OverlayRefusal::PositionOutOfOrder {
            node,
            expected: frame.next,
            found: bound.position,
        });
    }
    frame.next = SharePosition(frame.next.0.saturating_add(1));
    Ok(())
}

/// A core node of any family: what an opaque node holds and what erasure
/// produces.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CoreId
{
    /// A core value.
    Value(ValueId),
    /// A core computation.
    Computation(ComputationId),
    /// A core value type.
    ValueType(ValueTypeId),
    /// A core computation type.
    CompType(CompTypeId),
}

/// Why an overlay could not be erased. A refused erasure leaves the core
/// arena as it found it.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum EraseFault
{
    /// Validation refused the overlay, in its own vocabulary. Carried rather
    /// than translated, so the refusal arrives under the name of the condition.
    Refused(OverlayRefusal),
    /// An opaque node names no node of the core arena erasure writes into.
    UnresolvedOpaque
    {
        /// The opaque node.
        node: OverlayId,
    },
    /// The walk's own stacks disagreed with the validated overlay. Unreachable
    /// while every leg is bound beneath the body that reads it and every graft
    /// is assembled over the children its own tasks erased; kept so erasure
    /// fails closed rather than answering.
    MachineInvariant,
}

/// Erase a value overlay into the core arena.
///
/// # Specification
/// - requires: `core` is the arena the overlay's opaque nodes name.
/// - ensures: on success, the core value `root` stands for. Each graft mints
///   one core node, after its children and its children left to right; an
///   opaque node is its core id as it stands; a share erases its leg once,
///   before its body, and every occurrence of it is that one id. On refusal
///   `core` is truncated back to its entry watermark.
/// - provides: the total, policy-free erasure every duplication stance is
///   measured against. It takes no policy, and its output is node for node the
///   arena a hand-built unshared term mints when built in the same order.
/// - fails: [`EraseFault::Refused`] with the validation refusal before anything
///   is minted, [`EraseFault::UnresolvedOpaque`] for an opaque node the core
///   arena does not hold, and [`EraseFault::MachineInvariant`] when the walk's
///   own stacks break.
/// - panics: none.
/// - intension: one core node per graft and none per occurrence, so the erased
///   term is a core DAG of the overlay's size even where its expansion is
///   exponential. Indices are copied, never shifted: an occurrence reads its
///   leg's free indices where it stands, which is the reading a core DAG gives
///   a node it reaches twice.
///
/// # Errors
/// - [`EraseFault::Refused`] — the overlay does not validate from `root`.
/// - [`EraseFault::UnresolvedOpaque`] — an opaque node does not resolve.
/// - [`EraseFault::MachineInvariant`] — the walk's own stacks broke.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surfaces are the validation gate, the four
///   node kinds and the graft arms, separated by every former of every family
///   erased against a hand-built arena, a refusal of each kind leaving the core
///   arena unchanged, and the deep cases erased and run through the unshared
///   pipeline beside their hand-built references inside a small stack.
/// - witness: `overlay::tests::erasure_mints_every_former_of_every_family_in_order`
/// - witness: `overlay::tests::a_refused_erasure_leaves_the_core_arena_unchanged`
/// - witness:
///   `deep_evaluation::deep_evaluation::an_erased_value_chain_evaluates_byte_for_byte_as_the_unshared_one`
/// - witness:
///   `deep_readback::deep_readback::an_erased_value_chain_reads_back_byte_for_byte_as_the_unshared_one`
/// - witness:
///   `teardown::teardown::an_erased_deep_overlay_equals_the_unshared_chain_inside_a_small_stack`
#[inline]
pub fn erase_value(
    overlay: &Overlay,
    root: OverlayValueId,
    core: &mut CoreArena,
) -> Result<ValueId, EraseFault>
{
    let erased = erase(overlay, OverlayId::Value(root), core)?;
    let CoreId::Value(value) = erased
    else {
        return Err(EraseFault::MachineInvariant);
    };
    Ok(value)
}

/// Erase a computation overlay into the core arena.
///
/// # Specification
/// - requires: `core` is the arena the overlay's opaque nodes name.
/// - ensures: on success, the core computation `root` stands for, minted as
///   [`erase_value`] mints; on refusal `core` is truncated back to its entry
///   watermark.
/// - provides: the computation half of the policy-free erasure.
/// - fails: as [`erase_value`] fails.
/// - panics: none.
///
/// # Errors
/// - [`EraseFault::Refused`] — the overlay does not validate from `root`.
/// - [`EraseFault::UnresolvedOpaque`] — an opaque node does not resolve.
/// - [`EraseFault::MachineInvariant`] — the walk's own stacks broke.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is the computation root, separated
///   by a shared case over every computation former, a deep bind chain whose
///   base is opaque and whose shared leg sits under every binder, and a deep
///   curried application sharing its argument.
/// - witness: `overlay::tests::erasure_mints_every_former_of_every_family_in_order`
/// - witness:
///   `deep_evaluation::deep_evaluation::an_erased_bind_chain_evaluates_byte_for_byte_as_the_unshared_one`
/// - witness:
///   `deep_evaluation::deep_evaluation::an_erased_curried_application_evaluates_byte_for_byte_as_the_unshared_one`
/// - witness:
///   `deep_readback::deep_readback::an_erased_suspension_chain_reads_back_byte_for_byte_as_the_unshared_one`
#[inline]
pub fn erase_computation(
    overlay: &Overlay,
    root: OverlayCompId,
    core: &mut CoreArena,
) -> Result<ComputationId, EraseFault>
{
    let erased = erase(overlay, OverlayId::Computation(root), core)?;
    let CoreId::Computation(computation) = erased
    else {
        return Err(EraseFault::MachineInvariant);
    };
    Ok(computation)
}

/// Erase a value-type overlay into the core arena.
///
/// # Specification
/// - requires: `core` is the arena the overlay's opaque nodes name.
/// - ensures: on success, the core value type `root` stands for, minted as
///   [`erase_value`] mints; on refusal `core` is truncated back to its entry
///   watermark.
/// - provides: the value-type half of the policy-free erasure.
/// - fails: as [`erase_value`] fails.
/// - panics: none.
///
/// # Errors
/// - [`EraseFault::Refused`] — the overlay does not validate from `root`.
/// - [`EraseFault::UnresolvedOpaque`] — an opaque node does not resolve.
/// - [`EraseFault::MachineInvariant`] — the walk's own stacks broke.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is the value-type root, separated by
///   every value-type former and a deep chain of lifts.
/// - witness: `overlay::tests::erasure_mints_every_former_of_every_family_in_order`
/// - witness:
///   `teardown::teardown::an_erased_deep_overlay_equals_the_unshared_chain_inside_a_small_stack`
#[inline]
pub fn erase_value_type(
    overlay: &Overlay,
    root: OverlayValueTypeId,
    core: &mut CoreArena,
) -> Result<ValueTypeId, EraseFault>
{
    let erased = erase(overlay, OverlayId::ValueType(root), core)?;
    let CoreId::ValueType(value_type) = erased
    else {
        return Err(EraseFault::MachineInvariant);
    };
    Ok(value_type)
}

/// Erase a computation-type overlay into the core arena.
///
/// # Specification
/// - requires: `core` is the arena the overlay's opaque nodes name.
/// - ensures: on success, the core computation type `root` stands for, minted
///   as [`erase_value`] mints; on refusal `core` is truncated back to its entry
///   watermark.
/// - provides: the computation-type half of the policy-free erasure.
/// - fails: as [`erase_value`] fails.
/// - panics: none.
///
/// # Errors
/// - [`EraseFault::Refused`] — the overlay does not validate from `root`.
/// - [`EraseFault::UnresolvedOpaque`] — an opaque node does not resolve.
/// - [`EraseFault::MachineInvariant`] — the walk's own stacks broke.
///
/// # Adequacy
/// - hypothesis: L3 — the decision surface is the computation-type root,
///   separated by a share of a value type among the domains of a dependent and
///   a non-dependent function type.
/// - witness: `overlay::tests::erasure_mints_every_former_of_every_family_in_order`
#[inline]
pub fn erase_comp_type(
    overlay: &Overlay,
    root: OverlayCompTypeId,
    core: &mut CoreArena,
) -> Result<CompTypeId, EraseFault>
{
    let erased = erase(overlay, OverlayId::CompType(root), core)?;
    let CoreId::CompType(comp_type) = erased
    else {
        return Err(EraseFault::MachineInvariant);
    };
    Ok(comp_type)
}

/// Validate, then erase, restoring the core arena on refusal.
///
/// # Specification
/// - requires: `core` is the arena the overlay's opaque nodes name.
/// - ensures: the core node `root` stands for, or a refusal with `core` at its
///   entry watermark.
/// - provides: the one gate the four typed entry points share.
/// - fails: as [`erase_value`] fails.
/// - panics: none.
///
/// # Errors
/// - [`EraseFault::Refused`] — the overlay does not validate from `root`.
/// - [`EraseFault::UnresolvedOpaque`] — an opaque node does not resolve.
/// - [`EraseFault::MachineInvariant`] — the walk's own stacks broke.
fn erase(
    overlay: &Overlay,
    root: OverlayId,
    core: &mut CoreArena,
) -> Result<CoreId, EraseFault>
{
    overlay.validate(root).map_err(EraseFault::Refused)?;
    let mark = core.watermark();
    let mut erasure = Erasure {
        overlay,
        core,
        steps: Vec::from([Step::Enter(root)]),
        legs: Vec::new(),
        results: Vec::new(),
    };
    let outcome = erasure.run();
    if outcome.is_err() {
        erasure.core.truncate_to(mark);
    }
    outcome
}

/// One pending step of the erasure walk.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Step
{
    /// Erase one node, or queue what erasing it takes.
    Enter(OverlayId),
    /// Bind the erased leg on the result stack for the body that follows.
    Bind,
    /// Release the innermost bound leg once its body is erased.
    Unbind,
    /// Mint a graft over the children its own tasks erased.
    Assemble(OverlayId),
}

/// The erasure walk: its task stack, the legs bound around the current node
/// innermost last, and the erased nodes awaiting their parent.
struct Erasure<'run>
{
    /// The overlay erased.
    overlay: &'run Overlay,
    /// The core arena erased into.
    core: &'run mut CoreArena,
    /// The pending steps.
    steps: Vec<Step>,
    /// The erased legs of the shares around the current node.
    legs: Vec<CoreId>,
    /// The erased nodes awaiting their parent.
    results: Vec<CoreId>,
}

impl Erasure<'_>
{
    /// Drive the walk until its steps run out.
    ///
    /// # Specification
    /// - requires: the overlay validates from the root the steps hold.
    /// - ensures: the one erased root, with no leg left bound.
    /// - provides: the heap-only drive; depth costs steps, never host frames.
    /// - fails: [`EraseFault::UnresolvedOpaque`] for an opaque node the core
    ///   arena does not hold, and [`EraseFault::MachineInvariant`] when a stack
    ///   breaks.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`EraseFault::UnresolvedOpaque`] — an opaque node does not resolve.
    /// - [`EraseFault::MachineInvariant`] — a stack broke.
    fn run(&mut self) -> Result<CoreId, EraseFault>
    {
        while let Some(step) = self.steps.pop() {
            match step {
                | Step::Enter(node) => {
                    self.enter(node)?;
                },
                | Step::Bind => {
                    let Some(leg) = self.results.pop()
                    else {
                        return Err(EraseFault::MachineInvariant);
                    };
                    self.legs.push(leg);
                },
                | Step::Unbind => {
                    if self.legs.pop().is_none() {
                        return Err(EraseFault::MachineInvariant);
                    }
                },
                | Step::Assemble(node) => {
                    let assembled = self.assemble(node)?;
                    self.results.push(assembled);
                },
            }
        }
        let Some(erased) = self.results.pop()
        else {
            return Err(EraseFault::MachineInvariant);
        };
        if self.results.is_empty() && self.legs.is_empty() {
            Ok(erased)
        }
        else {
            Err(EraseFault::MachineInvariant)
        }
    }

    /// Erase one node, or queue what erasing it takes.
    ///
    /// # Specification
    /// - requires: `node` is reachable from a validated root.
    /// - ensures: an opaque node or an occurrence pushes its core id; a share
    ///   queues its leg, the bind, its body and the unbind, in that order; a
    ///   graft queues its children left to right and then its own assembly.
    /// - provides: the post-order the minting order follows.
    /// - fails: [`EraseFault::UnresolvedOpaque`] for an opaque node the core
    ///   arena does not hold, [`EraseFault::Refused`] for a node that does not
    ///   resolve, and [`EraseFault::MachineInvariant`] for an occurrence no
    ///   bound leg answers.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`EraseFault::UnresolvedOpaque`] — an opaque node does not resolve.
    /// - [`EraseFault::Refused`] — `node` does not resolve.
    /// - [`EraseFault::MachineInvariant`] — no bound leg answers.
    fn enter(
        &mut self,
        node: OverlayId,
    ) -> Result<(), EraseFault>
    {
        let shape = self.overlay.shape(node).map_err(EraseFault::Refused)?;
        match shape {
            | Shape::Opaque(held) => {
                let present = match held {
                    | CoreId::Value(id) => self.core.value(id).is_some(),
                    | CoreId::Computation(id) => self.core.computation(id).is_some(),
                    | CoreId::ValueType(id) => self.core.value_type(id).is_some(),
                    | CoreId::CompType(id) => self.core.comp_type(id).is_some(),
                };
                if !present {
                    return Err(EraseFault::UnresolvedOpaque { node });
                }
                self.results.push(held);
            },
            | Shape::Bound(bound) => {
                let distance = usize::try_from(bound.distance.0).unwrap_or(usize::MAX);
                let Some(&leg) = self
                    .legs
                    .len()
                    .checked_sub(1)
                    .and_then(|innermost| innermost.checked_sub(distance))
                    .and_then(|named| self.legs.get(named))
                else {
                    return Err(EraseFault::MachineInvariant);
                };
                self.results.push(leg);
            },
            | Shape::Shared(sharing) => {
                self.steps.push(Step::Unbind);
                self.steps.push(Step::Enter(sharing.body));
                self.steps.push(Step::Bind);
                self.steps.push(Step::Enter(sharing.leg));
            },
            | Shape::Grafted(children) => {
                self.steps.push(Step::Assemble(node));
                children.push_reversed(&mut self.steps, Step::Enter);
            },
        }
        Ok(())
    }

    /// Mint the graft `node` holds over its erased children.
    ///
    /// # Specification
    /// - requires: `node` is a graft whose children were erased onto the result
    ///   stack, leftmost deepest.
    /// - ensures: the children are popped and one core node of the graft's
    ///   former is minted over them.
    /// - provides: the one place a graft becomes a core node.
    /// - fails: [`EraseFault::MachineInvariant`] when `node` is not a graft or
    ///   a child is missing or of the wrong family.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`EraseFault::MachineInvariant`] — the graft or a child is missing.
    fn assemble(
        &mut self,
        node: OverlayId,
    ) -> Result<CoreId, EraseFault>
    {
        let overlay = self.overlay;
        match node {
            | OverlayId::Value(id) => {
                let Some(held) = overlay.value(id)
                else {
                    return Err(EraseFault::MachineInvariant);
                };
                let ValueNode::Grafted(ref graft) = *held
                else {
                    return Err(EraseFault::MachineInvariant);
                };
                let value = self.assemble_value(graft)?;
                Ok(CoreId::Value(value))
            },
            | OverlayId::Computation(id) => {
                let Some(&CompNode::Grafted(graft)) = overlay.computation(id)
                else {
                    return Err(EraseFault::MachineInvariant);
                };
                let computation = self.assemble_computation(graft)?;
                Ok(CoreId::Computation(computation))
            },
            | OverlayId::ValueType(id) => {
                let Some(held) = overlay.value_type(id)
                else {
                    return Err(EraseFault::MachineInvariant);
                };
                let ValueTypeNode::Grafted(ref graft) = *held
                else {
                    return Err(EraseFault::MachineInvariant);
                };
                let value_type = self.assemble_value_type(graft)?;
                Ok(CoreId::ValueType(value_type))
            },
            | OverlayId::CompType(id) => {
                let Some(&CompTypeNode::Grafted(graft)) = overlay.comp_type(id)
                else {
                    return Err(EraseFault::MachineInvariant);
                };
                let comp_type = self.assemble_comp_type(graft)?;
                Ok(CoreId::CompType(comp_type))
            },
        }
    }

    /// Mint one core value over its erased children.
    ///
    /// # Specification
    /// - requires: the graft's children are the topmost results, rightmost on
    ///   top.
    /// - ensures: the core value of the graft's former over those children.
    /// - provides: one arm per value former.
    /// - fails: [`EraseFault::MachineInvariant`] for a missing child.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`EraseFault::MachineInvariant`] — a child is missing.
    fn assemble_value(
        &mut self,
        graft: &ValueGraft,
    ) -> Result<ValueId, EraseFault>
    {
        match *graft {
            | ValueGraft::Variable { zone, index } => Ok(self.core.value_variable(zone, index)),
            | ValueGraft::Constant(index) => Ok(self.core.value_constant(index)),
            | ValueGraft::Unit => Ok(self.core.value_unit()),
            | ValueGraft::Literal(ref literal) => Ok(self.core.value_literal(literal.clone())),
            | ValueGraft::Pair(..) => {
                let second = self.value()?;
                let first = self.value()?;
                Ok(self.core.value_pair(first, second))
            },
            | ValueGraft::Injection(side, _) => {
                let body = self.value()?;
                Ok(self.core.value_injection(side, body))
            },
            | ValueGraft::Thunk(_) => {
                let body = self.computation()?;
                Ok(self.core.value_thunk(body))
            },
            | ValueGraft::Lift { ref target, .. } => {
                let body = self.value()?;
                Ok(self.core.value_lift(target.clone(), body))
            },
        }
    }

    /// Mint one core computation over its erased children.
    ///
    /// # Specification
    /// - requires: the graft's children are the topmost results, rightmost on
    ///   top.
    /// - ensures: the core computation of the graft's former over those
    ///   children.
    /// - provides: one arm per computation former.
    /// - fails: [`EraseFault::MachineInvariant`] for a missing child.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`EraseFault::MachineInvariant`] — a child is missing.
    fn assemble_computation(
        &mut self,
        graft: CompGraft,
    ) -> Result<ComputationId, EraseFault>
    {
        match graft {
            | CompGraft::Lambda(_) => {
                let body = self.computation()?;
                Ok(self.core.computation_lambda(body))
            },
            | CompGraft::Application(..) => {
                let argument = self.value()?;
                let head = self.computation()?;
                Ok(self.core.computation_application(head, argument))
            },
            | CompGraft::Return(_) => {
                let value = self.value()?;
                Ok(self.core.computation_return(value))
            },
            | CompGraft::Bind(..) => {
                let body = self.computation()?;
                let bound = self.computation()?;
                Ok(self.core.computation_bind(bound, body))
            },
            | CompGraft::Force(_) => {
                let value = self.value()?;
                Ok(self.core.computation_force(value))
            },
            | CompGraft::Case { .. } => {
                let on_right = self.computation()?;
                let on_left = self.computation()?;
                let scrutinee = self.value()?;
                Ok(self.core.computation_case(scrutinee, on_left, on_right))
            },
        }
    }

    /// Mint one core value type over its erased children.
    ///
    /// # Specification
    /// - requires: the graft's children are the topmost results, rightmost on
    ///   top.
    /// - ensures: the core value type of the graft's former over those
    ///   children.
    /// - provides: one arm per value-type former.
    /// - fails: [`EraseFault::MachineInvariant`] for a missing child.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`EraseFault::MachineInvariant`] — a child is missing.
    fn assemble_value_type(
        &mut self,
        graft: &ValueTypeGraft,
    ) -> Result<ValueTypeId, EraseFault>
    {
        match *graft {
            | ValueTypeGraft::Base(base) => Ok(self.core.value_type_base(base)),
            | ValueTypeGraft::Unit => Ok(self.core.value_type_unit()),
            | ValueTypeGraft::Product(..) => {
                let second = self.value_type()?;
                let first = self.value_type()?;
                Ok(self.core.value_type_product(first, second))
            },
            | ValueTypeGraft::Sum(..) => {
                let second = self.value_type()?;
                let first = self.value_type()?;
                Ok(self.core.value_type_sum(first, second))
            },
            | ValueTypeGraft::Thunk(_) => {
                let body = self.comp_type()?;
                Ok(self.core.value_type_thunk(body))
            },
            | ValueTypeGraft::Universe(ref level) => {
                Ok(self.core.value_type_universe(level.clone()))
            },
            | ValueTypeGraft::Lift { ref target, .. } => {
                let inner = self.value_type()?;
                Ok(self.core.value_type_lift(inner, target.clone()))
            },
            | ValueTypeGraft::Element { ref target, .. } => {
                let code = self.value()?;
                Ok(self.core.value_type_element(code, target.clone()))
            },
            | ValueTypeGraft::Abstract(atom) => Ok(self.core.value_type_abstract(atom)),
        }
    }

    /// Mint one core computation type over its erased children.
    ///
    /// # Specification
    /// - requires: the graft's children are the topmost results, rightmost on
    ///   top.
    /// - ensures: the core computation type of the graft's former over those
    ///   children.
    /// - provides: one arm per computation-type former.
    /// - fails: [`EraseFault::MachineInvariant`] for a missing child.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`EraseFault::MachineInvariant`] — a child is missing.
    fn assemble_comp_type(
        &mut self,
        graft: CompTypeGraft,
    ) -> Result<CompTypeId, EraseFault>
    {
        match graft {
            | CompTypeGraft::Returner(_) => {
                let result = self.value_type()?;
                Ok(self.core.comp_type_returner(result))
            },
            | CompTypeGraft::Arrow { .. } => {
                let codomain = self.comp_type()?;
                let domain = self.value_type()?;
                Ok(self.core.comp_type_arrow(domain, codomain))
            },
            | CompTypeGraft::Pi { .. } => {
                let codomain = self.comp_type()?;
                let domain = self.value_type()?;
                Ok(self.core.comp_type_pi(domain, codomain))
            },
        }
    }

    /// Pop an erased value.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the topmost result, when it is a value.
    /// - provides: the typed pop that catches a family the walk did not expect.
    /// - fails: [`EraseFault::MachineInvariant`] when the top is missing or of
    ///   another family.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`EraseFault::MachineInvariant`] — no value is on top.
    fn value(&mut self) -> Result<ValueId, EraseFault>
    {
        let Some(CoreId::Value(id)) = self.results.pop()
        else {
            return Err(EraseFault::MachineInvariant);
        };
        Ok(id)
    }

    /// Pop an erased computation.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the topmost result, when it is a computation.
    /// - provides: the typed pop that catches a family the walk did not expect.
    /// - fails: [`EraseFault::MachineInvariant`] when the top is missing or of
    ///   another family.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`EraseFault::MachineInvariant`] — no computation is on top.
    fn computation(&mut self) -> Result<ComputationId, EraseFault>
    {
        let Some(CoreId::Computation(id)) = self.results.pop()
        else {
            return Err(EraseFault::MachineInvariant);
        };
        Ok(id)
    }

    /// Pop an erased value type.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the topmost result, when it is a value type.
    /// - provides: the typed pop that catches a family the walk did not expect.
    /// - fails: [`EraseFault::MachineInvariant`] when the top is missing or of
    ///   another family.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`EraseFault::MachineInvariant`] — no value type is on top.
    fn value_type(&mut self) -> Result<ValueTypeId, EraseFault>
    {
        let Some(CoreId::ValueType(id)) = self.results.pop()
        else {
            return Err(EraseFault::MachineInvariant);
        };
        Ok(id)
    }

    /// Pop an erased computation type.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the topmost result, when it is a computation type.
    /// - provides: the typed pop that catches a family the walk did not expect.
    /// - fails: [`EraseFault::MachineInvariant`] when the top is missing or of
    ///   another family.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`EraseFault::MachineInvariant`] — no computation type is on top.
    fn comp_type(&mut self) -> Result<CompTypeId, EraseFault>
    {
        let Some(CoreId::CompType(id)) = self.results.pop()
        else {
            return Err(EraseFault::MachineInvariant);
        };
        Ok(id)
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::String;

    use gandr_core_term::CoreArena;
    use gandr_core_term::Zone;
    use gandr_kernel_strata::Level;
    use gandr_kernel_term::BaseType;
    use gandr_kernel_term::ConstantIndex;
    use gandr_kernel_term::DeBruijnIndex;
    use gandr_kernel_term::IntegerLiteral;
    use gandr_kernel_term::Literal;
    use gandr_kernel_term::Magnitude;
    use gandr_kernel_term::Side;
    use gandr_kernel_term::Sign;

    use super::Bound;
    use super::CompGraft;
    use super::CompNode;
    use super::CompTypeGraft;
    use super::CompTypeNode;
    use super::EraseFault;
    use super::Overlay;
    use super::OverlayCompId;
    use super::OverlayCompTypeId;
    use super::OverlayFamily;
    use super::OverlayFault;
    use super::OverlayId;
    use super::OverlayRefusal;
    use super::OverlayValueId;
    use super::OverlayValueTypeId;
    use super::OverlayWatermark;
    use super::ShareArity;
    use super::ShareDistance;
    use super::SharePosition;
    use super::Sharing;
    use super::ValueGraft;
    use super::ValueNode;
    use super::ValueTypeGraft;
    use super::ValueTypeNode;
    use super::erase_comp_type;
    use super::erase_computation;
    use super::erase_value;
    use super::erase_value_type;

    /// A grafted unit value.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a fresh value leaf.
    /// - provides: the legs and leaves the validation witnesses share.
    /// - panics: when a leaf mint is refused, which only the id ceiling causes.
    fn unit(overlay: &mut Overlay) -> OverlayValueId
    {
        overlay
            .mint_value(ValueNode::Grafted(ValueGraft::Unit))
            .expect("a leaf names no child")
    }

    /// A value occurrence `distance` shares out, at `position`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a fresh value occurrence.
    /// - provides: the occurrences the validation witnesses place.
    /// - panics: when a leaf mint is refused, which only the id ceiling causes.
    fn occurrence(
        overlay: &mut Overlay,
        distance: ShareDistance,
        position: SharePosition,
    ) -> OverlayValueId
    {
        overlay
            .mint_value(ValueNode::Bound(Bound { distance, position }))
            .expect("an occurrence names no child")
    }

    /// A value share of `leg` among `arity` occurrences in `body`.
    ///
    /// # Specification
    /// - requires: `leg` and `body` resolve in `overlay`.
    /// - ensures: a fresh value share.
    /// - provides: the shares the validation witnesses build.
    /// - panics: when the mint is refused, which the requirement excludes.
    fn share(
        overlay: &mut Overlay,
        arity: ShareArity,
        leg: OverlayId,
        body: OverlayValueId,
    ) -> OverlayValueId
    {
        overlay
            .mint_value(ValueNode::Shared(Sharing { arity, leg, body }))
            .expect("the leg and the body resolve")
    }

    /// A value pair of two nodes.
    ///
    /// # Specification
    /// - requires: both nodes resolve in `overlay`.
    /// - ensures: a fresh grafted pair.
    /// - provides: the two-child body the occurrence witnesses order.
    /// - panics: when the mint is refused, which the requirement excludes.
    fn pair(
        overlay: &mut Overlay,
        first: OverlayValueId,
        second: OverlayValueId,
    ) -> OverlayValueId
    {
        overlay
            .mint_value(ValueNode::Grafted(ValueGraft::Pair(first, second)))
            .expect("both components resolve")
    }

    #[test]
    fn minting_refuses_a_child_the_overlay_does_not_hold()
    {
        let mut elsewhere = Overlay::new();
        let foreign = unit(&mut elsewhere);
        let foreign_comp = elsewhere
            .mint_computation(CompNode::Grafted(CompGraft::Return(foreign)))
            .expect("the returned value resolves");

        let mut overlay = Overlay::new();
        assert_eq!(
            Err(OverlayFault::DanglingChild {
                child: OverlayId::Value(foreign)
            }),
            overlay.mint_value(ValueNode::Grafted(ValueGraft::Pair(foreign, foreign))),
            "a graft over a child this overlay never minted is refused"
        );
        assert_eq!(
            Err(OverlayFault::DanglingChild {
                child: OverlayId::Computation(foreign_comp)
            }),
            overlay.mint_value(ValueNode::Grafted(ValueGraft::Thunk(foreign_comp))),
            "and so is one across families"
        );
        assert_eq!(
            OverlayWatermark::default(),
            overlay.watermark(),
            "a refused mint leaves nothing behind"
        );

        let leg = unit(&mut overlay);
        let body = overlay
            .mint_computation(CompNode::Bound(Bound {
                distance: ShareDistance::from(0_u32),
                position: SharePosition::from(0_u32),
            }))
            .expect("an occurrence names no child");
        // An id carries no provenance, so the foreign leg is one past every
        // computation this overlay holds rather than the other overlay's first.
        let missing = OverlayCompId(7);
        assert_eq!(
            Err(OverlayFault::DanglingChild {
                child: OverlayId::Computation(missing)
            }),
            overlay.mint_computation(CompNode::Shared(Sharing {
                arity: ShareArity::from(1_u32),
                leg: OverlayId::Computation(missing),
                body,
            })),
            "a share's leg is a child like any other"
        );
        assert!(
            overlay
                .mint_computation(CompNode::Shared(Sharing {
                    arity: ShareArity::from(1_u32),
                    leg: OverlayId::Value(leg),
                    body,
                }))
                .is_ok(),
            "and a share whose leg and body resolve mints"
        );

        let result = elsewhere
            .mint_value_type(ValueTypeNode::Grafted(ValueTypeGraft::Unit))
            .expect("a leaf names no child");
        let codomain = elsewhere
            .mint_comp_type(CompTypeNode::Grafted(CompTypeGraft::Returner(result)))
            .expect("the result type resolves");
        let domain = overlay
            .mint_value_type(ValueTypeNode::Grafted(ValueTypeGraft::Unit))
            .expect("a leaf names no child");
        assert_eq!(
            Err(OverlayFault::DanglingChild {
                child: OverlayId::CompType(codomain)
            }),
            overlay.mint_comp_type(CompTypeNode::Grafted(CompTypeGraft::Arrow {
                domain,
                codomain
            })),
            "the type families check their children too"
        );
        assert_eq!(
            Err(OverlayFault::DanglingChild {
                child: OverlayId::Value(OverlayValueId(7))
            }),
            overlay.mint_value_type(ValueTypeNode::Grafted(ValueTypeGraft::Element {
                code: OverlayValueId(7),
                target: Level::zero(),
            })),
            "including the one child that crosses into the term families"
        );
    }

    #[test]
    fn validation_refuses_an_open_node_set_by_name()
    {
        let mut overlay = Overlay::new();
        let zero = ShareDistance::from(0_u32);
        let first = SharePosition::from(0_u32);

        let stray = occurrence(&mut overlay, zero, first);
        assert_eq!(
            Err(OverlayRefusal::OpenReference {
                node: OverlayId::Value(stray)
            }),
            overlay.validate(OverlayId::Value(stray)),
            "an occurrence with no share around it leaves the node set open"
        );

        let leg = unit(&mut overlay);
        let escaping = occurrence(&mut overlay, ShareDistance::from(1_u32), first);
        let one = share(
            &mut overlay,
            ShareArity::from(1_u32),
            OverlayId::Value(leg),
            escaping,
        );
        assert_eq!(
            Err(OverlayRefusal::OpenReference {
                node: OverlayId::Value(escaping)
            }),
            overlay.validate(OverlayId::Value(one)),
            "one share around an occurrence that counts two out leaves it open too"
        );

        let leg = unit(&mut overlay);
        let closed = occurrence(&mut overlay, zero, first);
        let shared = share(
            &mut overlay,
            ShareArity::from(1_u32),
            OverlayId::Value(leg),
            closed,
        );
        assert_eq!(
            Ok(()),
            overlay.validate(OverlayId::Value(shared)),
            "the same occurrence counting to the share around it closes"
        );
    }

    #[test]
    fn validation_refuses_an_occurrence_of_another_family()
    {
        let mut overlay = Overlay::new();
        let leg = unit(&mut overlay);
        let stray = overlay
            .mint_computation(CompNode::Bound(Bound {
                distance: ShareDistance::from(0_u32),
                position: SharePosition::from(0_u32),
            }))
            .expect("an occurrence names no child");
        let shared = overlay
            .mint_computation(CompNode::Shared(Sharing {
                arity: ShareArity::from(1_u32),
                leg: OverlayId::Value(leg),
                body: stray,
            }))
            .expect("the leg and the body resolve");
        assert_eq!(
            Err(OverlayRefusal::FamilyMismatch {
                node: OverlayId::Computation(stray),
                occurrence: OverlayFamily::Computation,
                leg: OverlayFamily::Value,
            }),
            overlay.validate(OverlayId::Computation(shared)),
            "a computation occurrence cannot stand for a value leg"
        );

        let produced = overlay
            .mint_computation(CompNode::Grafted(CompGraft::Return(leg)))
            .expect("the returned value resolves");
        let value_occurrence = occurrence_in_return(&mut overlay);
        let returned = overlay
            .mint_computation(CompNode::Shared(Sharing {
                arity: ShareArity::from(1_u32),
                leg: OverlayId::Computation(produced),
                body: value_occurrence,
            }))
            .expect("the leg and the body resolve");
        assert!(
            matches!(
                overlay.validate(OverlayId::Computation(returned)),
                Err(OverlayRefusal::FamilyMismatch {
                    occurrence: OverlayFamily::Value,
                    leg: OverlayFamily::Computation,
                    ..
                })
            ),
            "nor a value occurrence for a computation leg"
        );
    }

    /// `return x₀`, with `x₀` a value occurrence of the innermost share.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a fresh returner over a fresh value occurrence.
    /// - provides: the computation body whose occurrence is a value.
    /// - panics: when a mint is refused, which only the id ceiling causes.
    fn occurrence_in_return(overlay: &mut Overlay) -> OverlayCompId
    {
        let carried = occurrence(
            overlay,
            ShareDistance::from(0_u32),
            SharePosition::from(0_u32),
        );
        overlay
            .mint_computation(CompNode::Grafted(CompGraft::Return(carried)))
            .expect("the returned value resolves")
    }

    #[test]
    fn validation_holds_each_share_to_its_arity_in_preorder()
    {
        let mut overlay = Overlay::new();
        let zero = ShareDistance::from(0_u32);
        let first = SharePosition::from(0_u32);
        let second = SharePosition::from(1_u32);

        let leg = unit(&mut overlay);
        let body = unit(&mut overlay);
        let empty = share(
            &mut overlay,
            ShareArity::from(0_u32),
            OverlayId::Value(leg),
            body,
        );
        assert_eq!(
            Err(OverlayRefusal::ZeroArity {
                share: OverlayId::Value(empty)
            }),
            overlay.validate(OverlayId::Value(empty)),
            "a share standing for nothing is refused"
        );

        let leg = unit(&mut overlay);
        let only = occurrence(&mut overlay, zero, first);
        let short = share(
            &mut overlay,
            ShareArity::from(2_u32),
            OverlayId::Value(leg),
            only,
        );
        assert_eq!(
            Err(OverlayRefusal::MissingOccurrences {
                share: OverlayId::Value(short),
                arity: ShareArity::from(2_u32),
                next: second,
            }),
            overlay.validate(OverlayId::Value(short)),
            "a body holding fewer occurrences than the arity is refused at its share"
        );

        let leg = unit(&mut overlay);
        let taken = occurrence(&mut overlay, zero, first);
        let surplus = occurrence(&mut overlay, zero, second);
        let both = pair(&mut overlay, taken, surplus);
        let over = share(
            &mut overlay,
            ShareArity::from(1_u32),
            OverlayId::Value(leg),
            both,
        );
        assert_eq!(
            Err(OverlayRefusal::SurplusOccurrence {
                node: OverlayId::Value(surplus),
                arity: ShareArity::from(1_u32),
            }),
            overlay.validate(OverlayId::Value(over)),
            "an occurrence past the arity is refused where it stands"
        );

        let leg = unit(&mut overlay);
        let late = occurrence(&mut overlay, zero, second);
        let early = occurrence(&mut overlay, zero, first);
        let swapped = pair(&mut overlay, late, early);
        let misordered = share(
            &mut overlay,
            ShareArity::from(2_u32),
            OverlayId::Value(leg),
            swapped,
        );
        assert_eq!(
            Err(OverlayRefusal::PositionOutOfOrder {
                node: OverlayId::Value(late),
                expected: first,
                found: second,
            }),
            overlay.validate(OverlayId::Value(misordered)),
            "positions follow the body's preorder, leftmost first"
        );

        let leg = unit(&mut overlay);
        let left = occurrence(&mut overlay, zero, first);
        let right = occurrence(&mut overlay, zero, second);
        let ordered = pair(&mut overlay, left, right);
        let canonical = share(
            &mut overlay,
            ShareArity::from(2_u32),
            OverlayId::Value(leg),
            ordered,
        );
        assert_eq!(
            Ok(()),
            overlay.validate(OverlayId::Value(canonical)),
            "the same two occurrences in preorder close their share exactly"
        );
    }

    #[test]
    fn validation_refuses_a_node_reached_twice()
    {
        let mut overlay = Overlay::new();
        let leaf = unit(&mut overlay);
        let reused = pair(&mut overlay, leaf, leaf);
        assert_eq!(
            Err(OverlayRefusal::ReachedTwice {
                node: OverlayId::Value(leaf)
            }),
            overlay.validate(OverlayId::Value(reused)),
            "a node reused without a share is refused at its second arrival"
        );

        let leg = unit(&mut overlay);
        let left = occurrence(
            &mut overlay,
            ShareDistance::from(0_u32),
            SharePosition::from(0_u32),
        );
        let right = occurrence(
            &mut overlay,
            ShareDistance::from(0_u32),
            SharePosition::from(1_u32),
        );
        let body = pair(&mut overlay, left, right);
        let explicit = share(
            &mut overlay,
            ShareArity::from(2_u32),
            OverlayId::Value(leg),
            body,
        );
        assert_eq!(
            Ok(()),
            overlay.validate(OverlayId::Value(explicit)),
            "the same sharing named by a share is accepted"
        );
    }

    #[test]
    fn validation_refuses_a_root_the_overlay_does_not_hold()
    {
        let mut overlay = Overlay::new();
        let kept = unit(&mut overlay);
        let mark = overlay.watermark();
        let dropped = unit(&mut overlay);
        overlay.truncate_to(mark);
        assert_eq!(
            Err(OverlayRefusal::Unresolved {
                node: OverlayId::Value(dropped)
            }),
            overlay.validate(OverlayId::Value(dropped)),
            "a root truncated away names no node"
        );
        assert_eq!(Ok(()), overlay.validate(OverlayId::Value(kept)));
    }

    #[test]
    fn a_leg_counts_from_outside_its_share()
    {
        // outer = (inner = (⟨x₀, y₁⟩)[x₀ ← y₀])[y₀ y₁ ← ⟨⟩]: the inner share's leg
        // is y₀, counted from the outer frame because a leg stands outside its own
        // share, while y₁ in the inner body counts one frame further out.
        let mut overlay = Overlay::new();
        let outer_leg = unit(&mut overlay);
        let inner_leg = occurrence(
            &mut overlay,
            ShareDistance::from(0_u32),
            SharePosition::from(0_u32),
        );
        let inner_occurrence = occurrence(
            &mut overlay,
            ShareDistance::from(0_u32),
            SharePosition::from(0_u32),
        );
        let outer_occurrence = occurrence(
            &mut overlay,
            ShareDistance::from(1_u32),
            SharePosition::from(1_u32),
        );
        let body = pair(&mut overlay, inner_occurrence, outer_occurrence);
        let inner = share(
            &mut overlay,
            ShareArity::from(1_u32),
            OverlayId::Value(inner_leg),
            body,
        );
        let outer = share(
            &mut overlay,
            ShareArity::from(2_u32),
            OverlayId::Value(outer_leg),
            inner,
        );
        assert_eq!(
            Ok(()),
            overlay.validate(OverlayId::Value(outer)),
            "the leg counts from the shares around its share, the body from its own"
        );

        let self_reference = occurrence(
            &mut overlay,
            ShareDistance::from(0_u32),
            SharePosition::from(0_u32),
        );
        let body = occurrence(
            &mut overlay,
            ShareDistance::from(0_u32),
            SharePosition::from(0_u32),
        );
        let circular = share(
            &mut overlay,
            ShareArity::from(1_u32),
            OverlayId::Value(self_reference),
            body,
        );
        assert_eq!(
            Err(OverlayRefusal::OpenReference {
                node: OverlayId::Value(self_reference)
            }),
            overlay.validate(OverlayId::Value(circular)),
            "so a leg cannot name an occurrence of its own share"
        );
    }

    #[test]
    fn truncating_to_a_watermark_drops_later_nodes()
    {
        let mut overlay = Overlay::new();
        let kept = unit(&mut overlay);
        let kept_comp = overlay
            .mint_computation(CompNode::Grafted(CompGraft::Return(kept)))
            .expect("the returned value resolves");
        let mark = overlay.watermark();
        let dropped = unit(&mut overlay);
        let dropped_comp = overlay
            .mint_computation(CompNode::Grafted(CompGraft::Force(dropped)))
            .expect("the forced value resolves");
        let dropped_type = overlay
            .mint_value_type(ValueTypeNode::Grafted(ValueTypeGraft::Unit))
            .expect("a leaf names no child");
        let dropped_comp_type = overlay
            .mint_comp_type(CompTypeNode::Grafted(CompTypeGraft::Returner(dropped_type)))
            .expect("the result type resolves");

        overlay.truncate_to(mark);
        assert_eq!(mark, overlay.watermark());
        assert!(overlay.value(kept).is_some() && overlay.computation(kept_comp).is_some());
        assert!(
            overlay.value(dropped).is_none(),
            "a value past the mark is gone"
        );
        assert!(overlay.computation(dropped_comp).is_none());
        assert!(overlay.value_type(dropped_type).is_none());
        assert!(overlay.comp_type(dropped_comp_type).is_none());

        overlay.truncate_to(OverlayWatermark::default());
        assert_eq!(Overlay::new(), overlay, "the floor is the whole teardown");
    }

    /// Mint a computation node whose children resolve.
    ///
    /// # Specification
    /// - requires: every child of `node` resolves in `overlay`.
    /// - ensures: a fresh computation id.
    /// - provides: the terse mint the erasure witnesses build with.
    /// - panics: when the mint is refused, which the requirement excludes.
    fn computation(
        overlay: &mut Overlay,
        node: CompNode,
    ) -> OverlayCompId
    {
        overlay
            .mint_computation(node)
            .expect("every child resolves")
    }

    /// Mint a value-type node whose children resolve.
    ///
    /// # Specification
    /// - requires: every child of `node` resolves in `overlay`.
    /// - ensures: a fresh value-type id.
    /// - provides: the terse mint the erasure witnesses build with.
    /// - panics: when the mint is refused, which the requirement excludes.
    fn value_type(
        overlay: &mut Overlay,
        node: ValueTypeNode,
    ) -> OverlayValueTypeId
    {
        overlay.mint_value_type(node).expect("every child resolves")
    }

    /// Mint a computation-type node whose children resolve.
    ///
    /// # Specification
    /// - requires: every child of `node` resolves in `overlay`.
    /// - ensures: a fresh computation-type id.
    /// - provides: the terse mint the erasure witnesses build with.
    /// - panics: when the mint is refused, which the requirement excludes.
    fn comp_type(
        overlay: &mut Overlay,
        node: CompTypeNode,
    ) -> OverlayCompTypeId
    {
        overlay.mint_comp_type(node).expect("every child resolves")
    }

    /// Mint a value node whose children resolve.
    ///
    /// # Specification
    /// - requires: every child of `node` resolves in `overlay`.
    /// - ensures: a fresh value id.
    /// - provides: the terse mint the erasure witnesses build with.
    /// - panics: when the mint is refused, which the requirement excludes.
    fn value(
        overlay: &mut Overlay,
        node: ValueNode,
    ) -> OverlayValueId
    {
        overlay.mint_value(node).expect("every child resolves")
    }

    #[test]
    fn erasure_mints_every_former_of_every_family_in_order()
    {
        let target = Level::zero().succ().expect("level one exists");
        let magnitude =
            Magnitude::from_decimal_text(String::from("1")).expect("the digits are decimal");
        let literal = Literal::Integer(IntegerLiteral::new(Sign::NonNegative, magnitude));
        let innermost = DeBruijnIndex::from(0_u32);
        let first = ConstantIndex::from(0_usize);
        let second = ConstantIndex::from(1_usize);
        let zero = ShareDistance::from(0_u32);

        // The reference: every former minted by hand, in the order erasure walks —
        // a share's leg first, then each graft after its children, left to right.
        let mut reference = CoreArena::new();
        let held = reference.value_unit();
        let r_variable = reference.value_variable(Zone::Intuitionistic, innermost);
        let r_constant = reference.value_constant(first);
        let r_names = reference.value_pair(r_variable, r_constant);
        let r_literal = reference.value_literal(literal.clone());
        let r_injected = reference.value_injection(Side::Left, r_literal);
        let r_returned = reference.value_unit();
        let r_return = reference.computation_return(r_returned);
        let r_thunk = reference.value_thunk(r_return);
        let r_lifted = reference.value_unit();
        let r_lift = reference.value_lift(target.clone(), r_lifted);
        let r_suspended = reference.value_pair(r_thunk, r_lift);
        let r_wrapped = reference.value_pair(r_injected, r_suspended);
        let r_value = reference.value_pair(r_names, r_wrapped);

        let r_leg = reference.value_unit();
        let r_force = reference.computation_force(r_leg);
        let r_bound = reference.value_variable(Zone::Intuitionistic, innermost);
        let r_body = reference.computation_return(r_bound);
        let r_lambda = reference.computation_lambda(r_body);
        let r_application = reference.computation_application(r_lambda, held);
        let r_produced = reference.value_unit();
        let r_then = reference.computation_return(r_produced);
        let r_bind = reference.computation_bind(r_application, r_then);
        let r_case = reference.computation_case(r_leg, r_force, r_bind);

        let r_base = reference.value_type_base(BaseType::Integer);
        let r_unit = reference.value_type_unit();
        let r_sum = reference.value_type_sum(r_base, r_unit);
        let r_result = reference.value_type_unit();
        let r_returner = reference.comp_type_returner(r_result);
        let r_thunk_type = reference.value_type_thunk(r_returner);
        let r_universe = reference.value_type_universe(target.clone());
        let r_atom = reference.value_type_abstract(first);
        let r_lift_type = reference.value_type_lift(r_atom, target.clone());
        let r_code = reference.value_unit();
        let r_element = reference.value_type_element(r_code, target.clone());
        let r_codes = reference.value_type_product(r_lift_type, r_element);
        let r_universes = reference.value_type_product(r_universe, r_codes);
        let r_thunks = reference.value_type_product(r_thunk_type, r_universes);
        let r_value_type = reference.value_type_product(r_sum, r_thunks);

        let r_domain = reference.value_type_unit();
        let r_sealed = reference.value_type_abstract(second);
        let r_codomain = reference.comp_type_returner(r_sealed);
        let r_arrow = reference.comp_type_arrow(r_domain, r_codomain);
        let r_pi = reference.comp_type_pi(r_domain, r_arrow);

        // The overlay: the same four terms, the computation and the
        // computation type each sharing one leg between two occurrences.
        let mut core = CoreArena::new();
        let opaque = core.value_unit();
        let mut overlay = Overlay::new();

        let o_variable = value(
            &mut overlay,
            ValueNode::Grafted(ValueGraft::Variable {
                zone: Zone::Intuitionistic,
                index: innermost,
            }),
        );
        let o_constant = value(
            &mut overlay,
            ValueNode::Grafted(ValueGraft::Constant(first)),
        );
        let o_names = pair(&mut overlay, o_variable, o_constant);
        let o_literal = value(
            &mut overlay,
            ValueNode::Grafted(ValueGraft::Literal(literal)),
        );
        let o_injected = value(
            &mut overlay,
            ValueNode::Grafted(ValueGraft::Injection(Side::Left, o_literal)),
        );
        let o_returned = unit(&mut overlay);
        let o_return = computation(
            &mut overlay,
            CompNode::Grafted(CompGraft::Return(o_returned)),
        );
        let o_thunk = value(
            &mut overlay,
            ValueNode::Grafted(ValueGraft::Thunk(o_return)),
        );
        let o_lifted = unit(&mut overlay);
        let o_lift = value(
            &mut overlay,
            ValueNode::Grafted(ValueGraft::Lift {
                target: target.clone(),
                body: o_lifted,
            }),
        );
        let o_suspended = pair(&mut overlay, o_thunk, o_lift);
        let o_wrapped = pair(&mut overlay, o_injected, o_suspended);
        let o_value = pair(&mut overlay, o_names, o_wrapped);

        let o_leg = unit(&mut overlay);
        let o_scrutinee = occurrence(&mut overlay, zero, SharePosition::from(0_u32));
        let o_forced = occurrence(&mut overlay, zero, SharePosition::from(1_u32));
        let o_force = computation(&mut overlay, CompNode::Grafted(CompGraft::Force(o_forced)));
        let o_bound = value(
            &mut overlay,
            ValueNode::Grafted(ValueGraft::Variable {
                zone: Zone::Intuitionistic,
                index: innermost,
            }),
        );
        let o_body = computation(&mut overlay, CompNode::Grafted(CompGraft::Return(o_bound)));
        let o_lambda = computation(&mut overlay, CompNode::Grafted(CompGraft::Lambda(o_body)));
        let o_held = value(&mut overlay, ValueNode::Opaque(opaque));
        let o_application = computation(
            &mut overlay,
            CompNode::Grafted(CompGraft::Application(o_lambda, o_held)),
        );
        let o_produced = unit(&mut overlay);
        let o_then = computation(
            &mut overlay,
            CompNode::Grafted(CompGraft::Return(o_produced)),
        );
        let o_bind = computation(
            &mut overlay,
            CompNode::Grafted(CompGraft::Bind(o_application, o_then)),
        );
        let o_case = computation(
            &mut overlay,
            CompNode::Grafted(CompGraft::Case {
                scrutinee: o_scrutinee,
                on_left: o_force,
                on_right: o_bind,
            }),
        );
        let o_computation = computation(
            &mut overlay,
            CompNode::Shared(Sharing {
                arity: ShareArity::from(2_u32),
                leg: OverlayId::Value(o_leg),
                body: o_case,
            }),
        );

        let o_base = value_type(
            &mut overlay,
            ValueTypeNode::Grafted(ValueTypeGraft::Base(BaseType::Integer)),
        );
        let o_unit = value_type(&mut overlay, ValueTypeNode::Grafted(ValueTypeGraft::Unit));
        let o_sum = value_type(
            &mut overlay,
            ValueTypeNode::Grafted(ValueTypeGraft::Sum(o_base, o_unit)),
        );
        let o_result = value_type(&mut overlay, ValueTypeNode::Grafted(ValueTypeGraft::Unit));
        let o_returner = comp_type(
            &mut overlay,
            CompTypeNode::Grafted(CompTypeGraft::Returner(o_result)),
        );
        let o_thunk_type = value_type(
            &mut overlay,
            ValueTypeNode::Grafted(ValueTypeGraft::Thunk(o_returner)),
        );
        let o_universe = value_type(
            &mut overlay,
            ValueTypeNode::Grafted(ValueTypeGraft::Universe(target.clone())),
        );
        let o_atom = value_type(
            &mut overlay,
            ValueTypeNode::Grafted(ValueTypeGraft::Abstract(first)),
        );
        let o_lift_type = value_type(
            &mut overlay,
            ValueTypeNode::Grafted(ValueTypeGraft::Lift {
                inner: o_atom,
                target: target.clone(),
            }),
        );
        let o_code = unit(&mut overlay);
        let o_element = value_type(
            &mut overlay,
            ValueTypeNode::Grafted(ValueTypeGraft::Element {
                code: o_code,
                target,
            }),
        );
        let o_codes = value_type(
            &mut overlay,
            ValueTypeNode::Grafted(ValueTypeGraft::Product(o_lift_type, o_element)),
        );
        let o_universes = value_type(
            &mut overlay,
            ValueTypeNode::Grafted(ValueTypeGraft::Product(o_universe, o_codes)),
        );
        let o_thunks = value_type(
            &mut overlay,
            ValueTypeNode::Grafted(ValueTypeGraft::Product(o_thunk_type, o_universes)),
        );
        let o_value_type = value_type(
            &mut overlay,
            ValueTypeNode::Grafted(ValueTypeGraft::Product(o_sum, o_thunks)),
        );

        let o_domain = value_type(&mut overlay, ValueTypeNode::Grafted(ValueTypeGraft::Unit));
        let o_dependent = value_type(
            &mut overlay,
            ValueTypeNode::Bound(Bound {
                distance: zero,
                position: SharePosition::from(0_u32),
            }),
        );
        let o_plain = value_type(
            &mut overlay,
            ValueTypeNode::Bound(Bound {
                distance: zero,
                position: SharePosition::from(1_u32),
            }),
        );
        let o_sealed = value_type(
            &mut overlay,
            ValueTypeNode::Grafted(ValueTypeGraft::Abstract(second)),
        );
        let o_codomain = comp_type(
            &mut overlay,
            CompTypeNode::Grafted(CompTypeGraft::Returner(o_sealed)),
        );
        let o_arrow = comp_type(
            &mut overlay,
            CompTypeNode::Grafted(CompTypeGraft::Arrow {
                domain: o_plain,
                codomain: o_codomain,
            }),
        );
        let o_pi = comp_type(
            &mut overlay,
            CompTypeNode::Grafted(CompTypeGraft::Pi {
                domain: o_dependent,
                codomain: o_arrow,
            }),
        );
        let o_comp_type = comp_type(
            &mut overlay,
            CompTypeNode::Shared(Sharing {
                arity: ShareArity::from(2_u32),
                leg: OverlayId::ValueType(o_domain),
                body: o_pi,
            }),
        );

        let erased = (
            erase_value(&overlay, o_value, &mut core),
            erase_computation(&overlay, o_computation, &mut core),
            erase_value_type(&overlay, o_value_type, &mut core),
            erase_comp_type(&overlay, o_comp_type, &mut core),
        );
        assert_eq!(
            (Ok(r_value), Ok(r_case), Ok(r_value_type), Ok(r_pi)),
            erased,
            "each root erases to the id its hand-built term takes"
        );
        assert_eq!(
            reference, core,
            "and the arena holds node for node what the hand-built terms minted: one node \
             per graft, the opaque id as it stands, and one leg per share"
        );
    }

    #[test]
    fn a_refused_erasure_leaves_the_core_arena_unchanged()
    {
        let mut core = CoreArena::new();
        let kept = core.value_unit();
        let entry = core.clone();
        let mut overlay = Overlay::new();

        let stray = occurrence(
            &mut overlay,
            ShareDistance::from(0_u32),
            SharePosition::from(0_u32),
        );
        let wrapped = computation(&mut overlay, CompNode::Grafted(CompGraft::Return(stray)));
        assert_eq!(
            Err(EraseFault::Refused(OverlayRefusal::OpenReference {
                node: OverlayId::Value(stray)
            })),
            erase_computation(&overlay, wrapped, &mut core),
            "validation refuses in its own vocabulary"
        );
        assert_eq!(entry, core, "before anything is minted");

        // A core id one past every value the arena holds, so it cannot resolve.
        let foreign = {
            let mut elsewhere = CoreArena::new();
            let leaf = elsewhere.value_unit();
            let pair = elsewhere.value_pair(leaf, leaf);
            elsewhere.value_pair(pair, pair)
        };
        let leaf = unit(&mut overlay);
        let opaque = value(&mut overlay, ValueNode::Opaque(foreign));
        let both = pair(&mut overlay, leaf, opaque);
        assert_eq!(
            Err(EraseFault::UnresolvedOpaque {
                node: OverlayId::Value(opaque)
            }),
            erase_value(&overlay, both, &mut core),
            "an opaque id the core arena does not hold is refused where it stands"
        );
        assert_eq!(
            entry, core,
            "and the leaf minted before it is truncated away"
        );

        let leaf = unit(&mut overlay);
        let held = value(&mut overlay, ValueNode::Opaque(kept));
        let both = pair(&mut overlay, leaf, held);
        assert!(
            erase_value(&overlay, both, &mut core).is_ok(),
            "the same shape over an id the arena holds erases"
        );
    }
}
