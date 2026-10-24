//! A model slot a call omits, and the models that may answer it.
//!
//! A function quantifying over a model in its prefix block, `@[s : Model(S)]`,
//! binds one implicit parameter per component of `S`'s signature, and a call
//! omitting the slot nominates one hole per component. [`ModelSlot`] keeps
//! those holes together with every model in scope whose theory is `S` or
//! includes it, each as the values it passes for the components, in the holes'
//! order. The checker resolves the slot to the one candidate its constraints
//! leave and fills the holes with that candidate's components, or refuses the
//! call.
//!
//! # Items
//!
//! - [`ModelSlot`]: an omitted slot's holes and its candidates.
//! - [`Candidate`]: one model's component values.
//! - [`CandidatePlace`]: a candidate's place among its slot's.
//! - [`Survivors`]: the candidates a slot's constraints left.
//! - [`Beyond`]: how many survivors stand past the places a set names.

use alloc::vec::Vec;

use anodized::spec;

use crate::ValueId;
use crate::hole::HoleId;

#[cfg(test)]
mod tests;

/// One model that may answer a slot: the value it passes for each component,
/// in signature order, each closed — the member or nested record of a module.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Candidate
{
    /// The value passed for each component, in signature order.
    pub components: Vec<ValueId>,
}

/// A model slot a call omits, with the models in scope that may answer it.
///
/// It holds the hole nominated for each component, in signature order, and
/// each candidate holds one component per hole in the same order. The kernel
/// never reads it: the checker resolves the slot before the body crosses.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct ModelSlot
{
    /// The hole the call nominated for each component, in signature order.
    pub holes: Vec<HoleId>,
    /// The models in scope that may answer the slot, in the order the lowering
    /// met them.
    pub candidates: Vec<Candidate>,
}

/// A candidate's place among its slot's candidates, from zero.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CandidatePlace(usize);

impl From<usize> for CandidatePlace
{
    /// The place `place`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(place: usize) -> Self
    {
        Self(place)
    }
}

impl From<CandidatePlace> for usize
{
    /// The place's index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(place: CandidatePlace) -> Self
    {
        place.0
    }
}

/// How many candidates stand past the places [`Survivors`] names one by one.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Beyond(u32);

impl From<u32> for Beyond
{
    /// The count `count`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: u32) -> Self
    {
        Self(count)
    }
}

impl From<Beyond> for u32
{
    /// The count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: Beyond) -> Self
    {
        count.0
    }
}

/// The candidates a slot's constraints left: the places below
/// [`Survivors::NAMED`] one by one, and a count of those at or past it.
///
/// A refusal carrying it stays a plain value, and a slot whose survivors stand
/// past the named places still counts them.
///
/// # Specification
/// - requires: nothing to construct this data.
/// - ensures: each place below [`Survivors::NAMED`] is held at most once; the
///   places at or past it are counted, saturating.
/// - executable: none — the slot the places index is not held.
///
/// # Adequacy
/// - hypothesis: L3 — a slot two candidates answer names both.
/// - witness: `model::tests::survivors_name_each_place_once_and_count_the_rest`
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Survivors
{
    /// One bit per named place, the lowest for the first.
    named: u64,
    /// How many survivors stand at or past [`Survivors::NAMED`].
    beyond: Beyond,
}

impl Survivors
{
    /// How many places the set names one by one.
    pub const NAMED: CandidatePlace = CandidatePlace(64);

    /// The set with `place` added.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a place below [`Self::NAMED`] is held; any other raises the
    ///   count beyond by one, saturating.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — places below and past the named ones.
    /// - witness: `model::tests::survivors_name_each_place_once_and_count_the_rest`
    #[spec(ensures: |ret| usize::from(place) >= usize::from(Self::NAMED) || ret.places().any(|held| held == place))]
    #[inline]
    #[must_use]
    pub fn with(
        self,
        place: CandidatePlace,
    ) -> Self
    {
        u32::try_from(place.0)
            .ok()
            .and_then(|bit| 1_u64.checked_shl(bit))
            .map_or_else(
                || Self {
                    beyond: Beyond(self.beyond.0.saturating_add(1)),
                    ..self
                },
                |bit| Self {
                    named: self.named | bit,
                    ..self
                },
            )
    }

    /// The set with the count beyond the named places set to `beyond`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn beyond_named(
        self,
        beyond: Beyond,
    ) -> Self
    {
        Self { beyond, ..self }
    }

    /// The named places, ascending.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn places(self) -> impl Iterator<Item = CandidatePlace>
    {
        (0 .. Self::NAMED.0)
            .filter(move |&place| {
                u32::try_from(place)
                    .ok()
                    .and_then(|bit| self.named.checked_shr(bit))
                    .is_some_and(|shifted| shifted & 1 == 1)
            })
            .map(CandidatePlace)
    }

    /// How many survivors stand past the named places.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn beyond(self) -> Beyond
    {
        self.beyond
    }
}
