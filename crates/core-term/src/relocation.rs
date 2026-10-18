//! The renaming an id carries at its root: a node read a number of binders
//! further out or further in than it was minted, without a copy.
//!
//! # A relocation
//!
//! A [`Relocation`] is the de Bruijn shift `↑ᵏ_c` read as a renaming of the
//! intuitionistic zone: every index at or past the cutoff `c` moves by the
//! offset `k`, raised for a positive offset and lowered for a negative one,
//! and every index below the cutoff stays. The linear zone is never moved: no
//! former binds into it, so no rewrite of binders reaches it.
//!
//! A [`Relocated`] id is an arena node with a relocation pending at its root.
//! Raising a type into a deeper context and lowering one out of binders it
//! does not mention are updates of that relocation, so neither mints a node:
//! [`crate::shift_value_type`] and its siblings, and the strengthenings, answer
//! a relocated id over the node they were given.
//!
//! # Reading through a relocation
//!
//! A reader composes the relocation onto each child it reads, carried past the
//! binders the child's position crosses ([`Relocation::under`]) and fitted to
//! the child's support ([`CoreArena::place_value_type`] and its siblings), and
//! applies it where it reads a variable ([`Relocation::variable`]).
//! [`Relocated::settle`] is the eager reader: it mints the relocated tree,
//! entering only the nodes whose support the relocation moves, and is the one
//! walk left of the shifts and strengthenings — the boundary every consumer
//! that needs a plain id crosses.
//!
//! # Fitted to the support
//!
//! A relocation is kept fitted to the support of the node it is pending on:
//! the identity when no selected index stands at or past the cutoff, and
//! otherwise the cutoff raised to the least selected index at or past it. A
//! closed node therefore never carries a relocation, a relocated id equals the
//! plain one exactly when the relocation moves nothing, and two relocations
//! that move a node alike are one.
//!
//! # Composition
//!
//! Two relocations applied in turn fold into one only when the displacement
//! they make together is one step on the support: zero below some selected
//! index and one constant offset from it on. That is not always so: `↑¹_0`
//! then `↑¹_2` moves `0` to `1` and `3` to `5`, displacements one and two, so
//! no single relocation of `{0, 3}` does both. The arena's edges therefore stay
//! plain — a relocation stored on an edge would have to be composed with the
//! one a reader carries down to it, and that composition is not closed — and
//! only the id a caller holds carries one. A root update whose composition
//! does not fold settles the subject first.
//!
//! **Choice.** The relocation rides the id a caller holds, beside the plain
//! arena ids the nodes store, and the arena's read side is unchanged.
//! **Alternatives.** Every id relocated, the arena's reads answering a node
//! with its children composed, which hands an owned copy back at every read
//! of a relocated node and changes every read in the workspace; a relocation
//! stored on each edge, which composition does not close; the eager walk,
//! which copies every node a shift reaches. **Reversal.** A consumer whose
//! reads through relocations dominate its cost moves the composition into the
//! arena's reads.
//!
//! # References
//!
//! - Benjamin C. Pierce. _Types and Programming Languages_. MIT Press, 2002.
//!   `isbn:978-0-262-16209-8` — §6.2's shifting `↑ᵈ_c`, a negative `d` the
//!   lowering a substitution ends with.
//! - Conor `McBride`. "Everybody's Got To Be Somewhere." _MSFP 2018_, EPTCS
//!   275, pages 53–69. `doi:10.4204/EPTCS.275.6` — the support kept beside the
//!   term, which a relocation is fitted to.

use anodized::spec;
use gandr_kernel_term::DeBruijnIndex;
use quenchant_shape::shape::Maybe;

use crate::arena::CompTypeId;
use crate::arena::ComputationId;
use crate::arena::CoreArena;
use crate::arena::ValueId;
use crate::arena::ValueTypeId;
use crate::context::BinderDepth;
use crate::rewrite::Binders;
use crate::support::ThinningRef;
use crate::syntax::Zone;

/// Why a relocation has no single-step form.
pub mod folding
{
    /// The reason one relocation cannot stand for a move.
    #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub enum Absent
    {
        /// Applied in turn, two relocations move the support's indices by
        /// different offsets.
        Apart,
        /// The offset passes what a relocation holds.
        Wide,
    }
}

/// A signed count of binders an index moves by.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Offset(i64);

impl Offset
{
    /// The offset that moves nothing.
    pub(crate) const ZERO: Self = Self(0_i64);

    /// The offset raising by `amount`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn raise(amount: Binders) -> Self
    {
        Self(i64::from(u32::from(amount)))
    }

    /// The offset lowering by `amount`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn lower(amount: Binders) -> Self
    {
        Self(i64::from(u32::from(amount)).saturating_neg())
    }

    /// `position` moved by the offset, clamped to the index space.
    ///
    /// # Specification
    /// - requires: nothing; a move below zero or past the `u32` ceiling is
    ///   admissible and clamped.
    /// - ensures: `position + offset` when it lies in the index space; zero
    ///   below it and the ceiling past it.
    /// - provides: the variable a relocation reads an occurrence as.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a raise, a lowering and a lowering past zero separate
    ///   the sum from its clamp.
    /// - witness: `relocation::tests::a_relocation_moves_only_intuitionistic_indices_past_its_cutoff`
    #[spec(ensures: |ret| i64::from(u32::from(ret)) == i64::from(u32::from(position)).saturating_add(self.0).clamp(0, i64::from(u32::MAX)))]
    #[inline]
    pub(crate) fn moved(
        self,
        position: Binders,
    ) -> Binders
    {
        let moved = i64::from(u32::from(position)).saturating_add(self.0);
        Binders::from(u32::try_from(moved.max(0)).unwrap_or(u32::MAX))
    }
}

/// The renaming a node is read through: every intuitionistic index at or
/// past the cutoff moved by the offset.
///
/// # Specification
/// - executable: none — a data declaration. A relocation is the identity
///   exactly when its offset is zero, and then its cutoff is zero too, so the
///   derived equality is the renaming's.
///
/// # Adequacy
/// - hypothesis: L3 — fitting, composition and application are separated by
///   supports below, at and past the cutoff, and by the composition that does
///   not fold.
/// - witness: `relocation::tests::a_relocation_fits_to_its_support`
/// - witness: `relocation::tests::relocations_fold_exactly_when_the_support_moves_in_one_step`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Relocation
{
    /// How far a moved index moves; zero exactly for the identity.
    offset: i32,
    /// The least index moved; zero for the identity.
    cutoff: Binders,
}

impl Relocation
{
    /// The relocation that moves nothing.
    pub const IDENTITY: Self = Self {
        offset: 0_i32,
        cutoff: Binders::NONE,
    };

    /// The relocation raising every index at or past `cutoff` by `amount`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the identity for a zero `amount`; the raise otherwise.
    /// - fails: [`folding::Absent::Wide`] for an `amount` past `i32::MAX`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a zero, a small and a too-wide amount separate the
    ///   three answers.
    /// - witness: `relocation::tests::a_relocation_moves_only_intuitionistic_indices_past_its_cutoff`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(found) => if amount == Binders::NONE {
            found.offset == 0_i32 && found.cutoff == Binders::NONE
        } else {
            i64::from(found.offset) == i64::from(u32::from(amount)) && found.cutoff == cutoff
        },
        Maybe::Absent(_) => i32::try_from(u32::from(amount)).is_err(),
    })]
    #[inline]
    pub(crate) fn raise(
        amount: Binders,
        cutoff: Binders,
    ) -> Maybe<Self, folding::Absent>
    {
        match i32::try_from(u32::from(amount)) {
            Ok(0_i32) => Maybe::Present(Self::IDENTITY),
            Ok(offset) => Maybe::Present(Self { offset, cutoff }),
            Err(_wide) => Maybe::Absent(folding::Absent::Wide),
        }
    }

    /// The relocation lowering every index past the innermost `past` binders
    /// by `past`: the strengthening out of them, for a node that mentions
    /// none of them.
    ///
    /// # Specification
    /// - requires: a node it is pending on selects no index below `past`.
    /// - ensures: the identity past no binder; the lowering otherwise.
    /// - fails: [`folding::Absent::Wide`] for a `past` beyond `i32::MAX`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — no binder, one and two binders separate the identity
    ///   from the lowering and its depth.
    /// - witness: `relocation::tests::relocations_fold_exactly_when_the_support_moves_in_one_step`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(found) => if past == Binders::NONE {
            found.offset == 0_i32 && found.cutoff == Binders::NONE
        } else {
            i64::from(found.offset) == i64::from(u32::from(past)).saturating_neg()
                && found.cutoff == past
        },
        Maybe::Absent(_) => i32::try_from(u32::from(past)).is_err(),
    })]
    #[inline]
    pub(crate) fn lowering(past: Binders) -> Maybe<Self, folding::Absent>
    {
        match i32::try_from(u32::from(past)) {
            Ok(0_i32) => Maybe::Present(Self::IDENTITY),
            Ok(amount) => Maybe::Present(Self {
                offset: amount.saturating_neg(),
                cutoff: past,
            }),
            Err(_wide) => Maybe::Absent(folding::Absent::Wide),
        }
    }

    /// The offset an index at or past the cutoff moves by.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn offset(self) -> Offset
    {
        Offset(i64::from(self.offset))
    }

    /// The least index the relocation moves.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn cutoff(self) -> Binders
    {
        self.cutoff
    }

    /// The relocation read past `binders` more binders, as a child under
    /// them reads its parent's: the same move, its cutoff that much deeper.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the identity for the identity; otherwise the same offset at
    ///   the cutoff plus `binders`, clamped at the ceiling no context reaches.
    /// - provides: the relocation a reader composes onto a child.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the identity, and a relocation carried past zero and
    ///   one binder, separate a moved cutoff from a moved identity.
    /// - witness: `relocation::tests::a_relocation_moves_only_intuitionistic_indices_past_its_cutoff`
    #[spec(ensures: |ret| (self == Self::IDENTITY && ret == self)
        || (ret.offset == self.offset && ret.cutoff == self.cutoff.beyond(binders)))]
    #[inline]
    #[must_use]
    pub fn under(
        self,
        binders: Binders,
    ) -> Self
    {
        if self == Self::IDENTITY {
            return self;
        }
        Self {
            offset: self.offset,
            cutoff: self.cutoff.beyond(binders),
        }
    }

    /// The position `position` is read at through the relocation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn moved(
        self,
        position: Binders,
    ) -> Binders
    {
        if position < self.cutoff {
            position
        }
        else {
            self.offset().moved(position)
        }
    }

    /// The index a variable of `zone` at `index` is read at through the
    /// relocation.
    ///
    /// # Specification
    /// - requires: the relocation is pending on a node that selects `index`, or
    ///   one of its children read through it.
    /// - ensures: a linear index and an intuitionistic one below the cutoff
    ///   unchanged; an intuitionistic one at or past it moved by the offset.
    /// - provides: the application of a relocation where a variable is read.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a linear index, an index below the cutoff, one at it
    ///   and one past it, raised and lowered, separate the zone, the cutoff and
    ///   the sign.
    /// - witness: `relocation::tests::a_relocation_moves_only_intuitionistic_indices_past_its_cutoff`
    #[spec(ensures: |ret| match zone {
        Zone::Linear => ret == index,
        Zone::Intuitionistic => u32::from(index) < u32::from(self.cutoff) && ret == index
            || u32::from(index) >= u32::from(self.cutoff)
                && i64::from(u32::from(ret)) == i64::from(u32::from(index)).saturating_add(i64::from(self.offset)).clamp(0, i64::from(u32::MAX)),
    })]
    #[inline]
    #[must_use]
    pub fn variable(
        self,
        zone: Zone,
        index: DeBruijnIndex,
    ) -> DeBruijnIndex
    {
        match zone {
            Zone::Linear => index,
            Zone::Intuitionistic => {
                DeBruijnIndex::from(u32::from(self.moved(Binders::from(u32::from(index)))))
            },
        }
    }

    /// The relocation fitted to `support`: the identity when it moves none of
    /// the support's indices, and otherwise the same offset at the least
    /// selected index at or past the cutoff.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the identity, or a relocation of the same offset whose cutoff
    ///   is selected by `support` and is the least selected index at or past
    ///   the cutoff given.
    /// - provides: the canonical form ids are compared in.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an empty support, a support below the cutoff, one at
    ///   it and one past it, and a zero offset, separate the identity from the
    ///   raised cutoff.
    /// - witness: `relocation::tests::a_relocation_fits_to_its_support`
    #[spec(ensures: |ret| ret == Self::IDENTITY
        || (ret.offset == self.offset
            && support.outside(Zone::Intuitionistic, BinderDepth::from(usize::try_from(u32::from(self.cutoff)).unwrap_or(usize::MAX))).next()
                == Some(DeBruijnIndex::from(u32::from(ret.cutoff)))))]
    #[inline]
    pub(crate) fn fitted(
        self,
        support: ThinningRef<'_>,
    ) -> Self
    {
        if self.offset == 0_i32 {
            return Self::IDENTITY;
        }
        let from = BinderDepth::from(usize::try_from(u32::from(self.cutoff)).unwrap_or(usize::MAX));
        support
            .outside(Zone::Intuitionistic, from)
            .next()
            .map_or(Self::IDENTITY, |first| Self {
                offset: self.offset,
                cutoff: Binders::from(u32::from(first)),
            })
    }

    /// The one relocation that moves `support` as `self` and then `next` do,
    /// fitted to it.
    ///
    /// # Specification
    /// - requires: `self` is fitted to `support`, and `next` is a relocation of
    ///   the scope `self` moves `support` into.
    /// - ensures: a relocation that moves every index of `support` where the
    ///   two in turn move it.
    /// - fails: [`folding::Absent::Apart`] when the two in turn move the
    ///   support's indices by more than one offset past a zero prefix;
    ///   [`folding::Absent::Wide`] when the one offset passes `i32`.
    /// - panics: none.
    /// - intension: one pass over the support's intuitionistic indices.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two raises that fold, two that do not, a raise undone
    ///   by a lowering, and an empty support separate the fold, the refusal and
    ///   the identity.
    /// - witness: `relocation::tests::relocations_fold_exactly_when_the_support_moves_in_one_step`
    #[spec(ensures: |ret| match ret {
        Maybe::Present(folded) => support.indices(Zone::Intuitionistic).all(|index| {
            let position = Binders::from(u32::from(index));
            folded.moved(position) == next.moved(self.moved(position))
        }),
        Maybe::Absent(_) => true,
    })]
    pub(crate) fn then(
        self,
        next: Self,
        support: ThinningRef<'_>,
    ) -> Maybe<Self, folding::Absent>
    {
        let mut folded = Self::IDENTITY;
        for index in support.indices(Zone::Intuitionistic) {
            let position = Binders::from(u32::from(index));
            let moved = next.moved(self.moved(position));
            let displacement =
                i64::from(u32::from(moved)).saturating_sub(i64::from(u32::from(position)));
            if folded == Self::IDENTITY {
                if displacement != 0_i64 {
                    let Ok(offset) = i32::try_from(displacement)
                    else {
                        return Maybe::Absent(folding::Absent::Wide);
                    };
                    folded = Self {
                        offset,
                        cutoff: position,
                    };
                }
            }
            else if displacement != i64::from(folded.offset) {
                return Maybe::Absent(folding::Absent::Apart);
            }
        }
        Maybe::Present(folded)
    }
}

/// A node of one of the arena's families with a relocation pending at its
/// root: the node read through the relocation.
///
/// # Specification
/// - executable: none — a data declaration. Made by a root update or by
///   [`CoreArena::place_value_type`] and its siblings, its relocation is fitted
///   to the node's support, so a relocated id equals the plain one exactly when
///   it moves nothing.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Relocated<Id>
{
    /// The node, as it stands in the arena.
    node: Id,
    /// The relocation the node is read through.
    at: Relocation,
}

impl<Id: Copy> Relocated<Id>
{
    /// The node `node` read through `at`, which is fitted to its support.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn pending(
        node: Id,
        at: Relocation,
    ) -> Self
    {
        Self { node, at }
    }

    /// The node, as it stands in the arena.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn node(self) -> Id
    {
        self.node
    }

    /// The relocation the node is read through.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn relocation(self) -> Relocation
    {
        self.at
    }
}

impl<Id> From<Id> for Relocated<Id>
{
    /// The node read as it stands.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(node: Id) -> Self
    {
        Self {
            node,
            at: Relocation::IDENTITY,
        }
    }
}

impl CoreArena
{
    /// The value `node` read through `at`, fitted to its support.
    ///
    /// # Specification
    /// - requires: nothing; a dangling id keeps `at` as given.
    /// - ensures: `node` under `at` fitted to the node's support.
    /// - provides: a child of a relocated node, as a reader composes it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Relocation::fitted`], through the support the
    ///   arena carries.
    /// - witness: `relocation::tests::a_relocation_fits_to_its_support`
    #[spec(ensures: |ret| ret.node() == node
        && ret.relocation() == self.value_support(node).map_or(at, |support| at.fitted(support.view())))]
    #[inline]
    #[must_use]
    pub fn place_value(
        &self,
        node: ValueId,
        at: Relocation,
    ) -> Relocated<ValueId>
    {
        if at.offset == 0_i32 {
            return Relocated::from(node);
        }
        let at = self
            .value_support(node)
            .map_or(at, |support| at.fitted(support.view()));
        Relocated { node, at }
    }

    /// The computation `node` read through `at`, fitted to its support.
    ///
    /// # Specification
    /// - requires: nothing; a dangling id keeps `at` as given.
    /// - ensures: `node` under `at` fitted to the node's support.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::place_value`].
    /// - witness: `relocation::tests::a_relocation_fits_to_its_support`
    #[spec(ensures: |ret| ret.node() == node
        && ret.relocation()
            == self.computation_support(node).map_or(at, |support| at.fitted(support.view())))]
    #[inline]
    #[must_use]
    pub fn place_computation(
        &self,
        node: ComputationId,
        at: Relocation,
    ) -> Relocated<ComputationId>
    {
        if at.offset == 0_i32 {
            return Relocated::from(node);
        }
        let at = self
            .computation_support(node)
            .map_or(at, |support| at.fitted(support.view()));
        Relocated { node, at }
    }

    /// The value type `node` read through `at`, fitted to its support.
    ///
    /// # Specification
    /// - requires: nothing; a dangling id keeps `at` as given.
    /// - ensures: `node` under `at` fitted to the node's support.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::place_value`].
    /// - witness: `relocation::tests::a_relocation_fits_to_its_support`
    #[spec(ensures: |ret| ret.node() == node
        && ret.relocation()
            == self.value_type_support(node).map_or(at, |support| at.fitted(support.view())))]
    #[inline]
    #[must_use]
    pub fn place_value_type(
        &self,
        node: ValueTypeId,
        at: Relocation,
    ) -> Relocated<ValueTypeId>
    {
        if at.offset == 0_i32 {
            return Relocated::from(node);
        }
        let at = self
            .value_type_support(node)
            .map_or(at, |support| at.fitted(support.view()));
        Relocated { node, at }
    }

    /// The computation type `node` read through `at`, fitted to its support.
    ///
    /// # Specification
    /// - requires: nothing; a dangling id keeps `at` as given.
    /// - ensures: `node` under `at` fitted to the node's support.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Self::place_value`].
    /// - witness: `relocation::tests::a_relocation_fits_to_its_support`
    #[spec(ensures: |ret| ret.node() == node
        && ret.relocation()
            == self.comp_type_support(node).map_or(at, |support| at.fitted(support.view())))]
    #[inline]
    #[must_use]
    pub fn place_comp_type(
        &self,
        node: CompTypeId,
        at: Relocation,
    ) -> Relocated<CompTypeId>
    {
        if at.offset == 0_i32 {
            return Relocated::from(node);
        }
        let at = self
            .comp_type_support(node)
            .map_or(at, |support| at.fitted(support.view()));
        Relocated { node, at }
    }
}

#[cfg(test)]
mod tests;
