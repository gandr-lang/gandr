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

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use anodized::spec;
use gandr_core_term::CompTypeId;
use gandr_core_term::ComputationId;
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
                        | Shape::Opaque => {},
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
    /// An opaque core node.
    Opaque,
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
            | Self::Opaque | Self::Bound(_) => Children::Leaf,
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
            | Self::Opaque(_) => Shape::Opaque,
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
            | Self::Opaque(_) => Shape::Opaque,
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
            | Self::Opaque(_) => Shape::Opaque,
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
            | Self::Opaque(_) => Shape::Opaque,
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

#[cfg(test)]
mod tests
{
    use gandr_kernel_strata::Level;

    use super::Bound;
    use super::CompGraft;
    use super::CompNode;
    use super::CompTypeGraft;
    use super::CompTypeNode;
    use super::Overlay;
    use super::OverlayCompId;
    use super::OverlayFamily;
    use super::OverlayFault;
    use super::OverlayId;
    use super::OverlayRefusal;
    use super::OverlayValueId;
    use super::OverlayWatermark;
    use super::ShareArity;
    use super::ShareDistance;
    use super::SharePosition;
    use super::Sharing;
    use super::ValueGraft;
    use super::ValueNode;
    use super::ValueTypeGraft;
    use super::ValueTypeNode;

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
}
