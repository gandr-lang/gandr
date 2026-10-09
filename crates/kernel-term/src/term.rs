//! The term language: [`Value`] on the positive side and [`Computation`] on the
//! negative side, together with the reference forms [`DeBruijnIndex`] and
//! [`ConstantIndex`] and the injection [`Side`].
//!
//! Terms are nameless. A bound value variable is a [`DeBruijnIndex`] counting
//! binders outward from its use site, so α-equivalence is syntactic identity
//! and no name capture is representable. A [`Value::Constant`] names a prior
//! declaration by its admission position.
//!
//! The vocabulary is closed: no hole, metavariable, mark, annotation, effect
//! row, handler, or control operator exists to be represented.
//!
//! # Children are ids, and the derived relations are shallow
//!
//! A node's children are typed arena ids ([`ValueId`], [`ComputationId`])
//! rather than owned pointers; leaf payloads stay inline. Because an id is
//! `Copy`, the derived `Clone`, `Drop`, `PartialEq`, `Eq` and `Hash` are
//! **shallow** — they do not walk term depth — which is what retires the
//! hand-written iterative destructor an owned-tree representation needs and
//! makes arena teardown a flat vector drop.
//!
//! **The derived equality is child-id equality, not structural equality.** Two
//! structurally equal subterms need not share an id, because the kernel
//! preserves the sharing a decode handed it and never creates more. Every use
//! site therefore either compares only inline leaf payloads or resolves ids
//! explicitly; the format's deduplication is keyed on encoded content, never on
//! a node's derived equality.
//!
//! [`ValueId`]: crate::ValueId
//! [`ComputationId`]: crate::ComputationId

use gandr_kernel_strata::Level;

use crate::arena::CompTypeId;
use crate::arena::ComputationId;
use crate::arena::ValueId;
use crate::arena::ValueTypeId;
use crate::base::Literal;

/// A bound value variable, as a de Bruijn index counting binders outward: `0`
/// is the nearest enclosing binder.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DeBruijnIndex(u32);

impl From<u32> for DeBruijnIndex
{
    /// The index for a binder distance.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: u32) -> Self
    {
        Self(index)
    }
}

impl From<DeBruijnIndex> for u32
{
    /// The binder distance the index carries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: DeBruijnIndex) -> Self
    {
        index.0
    }
}

/// A reference to a prior declaration by its admission position, where `0` is
/// the first admitted declaration.
///
/// An admission position and a subterm-table index are two different things
/// that both spell as an integer, and confusing them is the format's most
/// available mistake; the wrapper is what stops one being passed where the
/// other belongs.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ConstantIndex(usize);

impl From<usize> for ConstantIndex
{
    /// The index for an admission position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: usize) -> Self
    {
        Self(index)
    }
}

impl From<ConstantIndex> for usize
{
    /// The admission position the index carries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: ConstantIndex) -> Self
    {
        index.0
    }
}

/// The side of a sum injection.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Side
{
    /// The left injection, into the left summand of `A + B`.
    Left,
    /// The right injection, into the right summand of `A + B`.
    Right,
}

/// A value: the positive fragment of the term vocabulary.
///
/// Values are the total, thunkable half of the polarity split. No value
/// constructor introduces a computation effect; the only value embedding a
/// computation is [`Self::Thunk`], and a thunk suspends rather than runs it.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Value
{
    /// A bound value variable.
    Variable(DeBruijnIndex),
    /// A reference to a prior declaration.
    Constant(ConstantIndex),
    /// The unique inhabitant of the unit type.
    Unit,
    /// A base-type literal.
    Literal(Literal),
    /// A pair, introducing the product `A × B`.
    Pair(ValueId, ValueId),
    /// A sum injection, introducing `A + B` on the given side.
    Injection(Side, ValueId),
    /// A thunk, suspending a computation into the value type `U C`.
    Thunk(ComputationId),
    /// An explicit universe lift: given `body : A` with `A`'s level strictly
    /// below `target`, this value inhabits `Lift A target`.
    ///
    /// The lift is written, never inferred: a bare `body : A` does not inhabit
    /// `Lift A target` on its own, because there is no implicit cumulativity.
    Lift
    {
        /// The target universe level of the lift.
        target: Level,
        /// The value being lifted.
        body: ValueId,
    },
    /// The code of a value type: `⌜A⌝`, an inhabitant of the value universe at
    /// `A`'s level.
    Quote(ValueTypeId),
    /// The code of a computation type: `⌜C⌝`, an inhabitant of the
    /// computation universe at `C`'s level.
    QuoteComputation(CompTypeId),
}

/// A computation: the negative fragment of the term vocabulary.
///
/// The eliminators — application, force, bind, case — synthesize; the
/// introductions — lambda, return — check against an expected computation type.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Computation
{
    /// A lambda `λ. M`, binding one value variable; introduces `A → C`.
    Lambda(ComputationId),
    /// An application `M v` of a computation to a value argument.
    Application(ComputationId, ValueId),
    /// A returner `return v`, introducing `F A`.
    Return(ValueId),
    /// A sequencing bind `x ← M; N`, binding the value `M` returns into `N`.
    Bind(ComputationId, ComputationId),
    /// A force `force v` of a thunk value `v : U C`, running it as `C`.
    Force(ValueId),
    /// A sum elimination, binding the injected value into each branch.
    Case
    {
        /// The scrutinee value, of a sum type.
        scrutinee: ValueId,
        /// The left branch, checked with the left summand bound.
        on_left: ComputationId,
        /// The right branch, checked with the right summand bound.
        on_right: ComputationId,
    },
}
