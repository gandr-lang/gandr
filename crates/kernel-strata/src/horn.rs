//! The crate-internal Horn machinery of Bezem–Coquand loop-checking: compiled
//! clause systems over level variables extended with the pinned bottom
//! generator, the uniform-shift firing rule, the least-model saturation, and
//! the bounded instrumented forward derivation that extracts checkable
//! evidence.
//!
//! The module is private, so everything here except the re-exported vocabulary
//! stays crate-internal. The public vocabulary — constraints, posets, evidence
//! — lives in the landmark-poset and entailment modules and compiles down to
//! these clause systems through one documented, deterministic enumeration, so
//! the clause indices carried by evidence mean the same thing on both sides of
//! the oracle/validator boundary.
//!
//! Correspondence with Marc Bezem and Thierry Coquand, "Loop-checking and the
//! uniform word problem for join-semilattices with an inflationary
//! endomorphism", *Theoretical Computer Science* 913 (2022), 1–7,
//! `doi:10.1016/j.tcs.2022.01.017`:
//!
//! * A clause `body → head` stands for the infinite family of its upward shifts
//!   `body+k → head+k` with `k ≥ min_shift` — the finitely represented shifted
//!   system of section 2, where `min_shift = 1` realizes the query
//!   transformation of lemma 2.1. Predecessor clauses are implicit: a model is
//!   stored as its per-variable maximum, which is the downward-closed atom set
//!   of section 3.
//! * [`fire`] is lemma 3.1: one min-and-compare decides what the whole shift
//!   family forces from a model.
//! * [`saturate`] is theorem 3.2 by monotone rounds, with the small-model
//!   property of corollary 4.2 turning "a finite value passed the bound" into
//!   "this component is infinite".
//! * [`derive_targets`] is the forward reasoning of section 2, instrumented
//!   with a step log so admission and entailment can hand back replayable
//!   derivations instead of asking for trust.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;

use crate::level::LevelConstant;
use crate::level::LevelError;
use crate::level::LevelOffset;
use crate::level::LevelVar;

/// A Horn atom offset in the shifted clause system.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct HornOffset(u128);

impl HornOffset
{
    /// The zero atom offset.
    pub const ZERO: Self = Self(0_u128);

    /// The unit atom offset.
    pub const ONE: Self = Self(1_u128);

    /// Checked addition in the atom-offset domain.
    ///
    /// # Specification
    /// - requires: nothing; adversarial magnitudes are admissible and are the
    ///   reason the sum is checked.
    /// - ensures: returns the sum when it fits the `u128` range.
    /// - provides: the offset arithmetic of the query encoding.
    /// - fails: [`LevelError::Overflow`] when the sum leaves the range.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LevelError::Overflow`] — the sum passed the `u128` range.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, ordinary sums, the exact u128 ceiling and one
    ///   step beyond expose incorrect addition and overflow guards by exact
    ///   results.
    /// - witness: `horn::tests::offset_arithmetic_covers_zero_equality_and_ceiling`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().ok().map(|value| u128::from(*value)) == self.0.checked_add(rhs.0))]
    pub fn checked_add(
        self,
        rhs: Self,
    ) -> Result<Self, LevelError>
    {
        self.0
            .checked_add(rhs.0)
            .map(Self)
            .ok_or(LevelError::Overflow)
    }

    /// Checked addition of a clause-family shift.
    ///
    /// # Specification
    /// - requires: nothing; adversarial shifts are admissible and are the
    ///   reason the sum is checked.
    /// - ensures: returns the shifted offset when it fits the `u128` range.
    /// - provides: the single arithmetic step of clause-instance firing.
    /// - fails: [`LevelError::Overflow`] when the shifted sum leaves the range.
    /// - panics: none.
    ///
    /// # Errors
    /// [`LevelError::Overflow`] — the shifted sum passed the `u128` range.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero and positive shifts at ordinary values, the
    ///   exact u128 ceiling and one step beyond distinguish a changed shift, a
    ///   guard off by one and wrapping arithmetic by exact results.
    /// - witness: `horn::tests::offset_arithmetic_covers_zero_equality_and_ceiling`
    #[inline]
    #[spec(ensures: |ret| ret.as_ref().ok().map(|value| u128::from(*value)) == self.0.checked_add(u128::from(shift)))]
    pub fn checked_add_shift(
        self,
        shift: HornShift,
    ) -> Result<Self, LevelError>
    {
        self.0
            .checked_add(u128::from(shift))
            .map(Self)
            .ok_or(LevelError::Overflow)
    }

    /// Saturating subtraction in the atom-offset domain.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns `self - rhs`, and zero wherever `rhs` exceeds `self`.
    /// - provides: the floored-at-zero difference a clause's gain is measured
    ///   with, where a conclusion below its body is no gain rather than a
    ///   negative one.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — subtrahends immediately below, equal to and above the
    ///   minuend distinguish reversed operands, wrapping and an incorrect zero
    ///   boundary by exact floored differences.
    /// - witness: `horn::tests::offset_arithmetic_covers_zero_equality_and_ceiling`
    #[spec(ensures: |ret| u128::from(ret) == self.0.saturating_sub(rhs.0))]
    #[inline]
    #[must_use]
    pub fn saturating_sub(
        self,
        rhs: Self,
    ) -> Self
    {
        Self(self.0.saturating_sub(rhs.0))
    }

    /// The upward shift that carries a zero-offset atom to this offset.
    ///
    /// This is the explicit cross-domain projection for the cases where the
    /// theory starts at zero and shifts upward; it replaces a blanket
    /// conversion between atom offsets and clause-family shifts.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the shift whose value is this offset, which is the
    ///   shift carrying a zero-offset atom to it.
    /// - provides: the sanctioned crossing from the offset domain into the
    ///   shift domain, named per site rather than opened as a conversion.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, ordinary magnitudes and the u128 ceiling are
    ///   used in shifted addition; exact sums and overflow refusals expose
    ///   altered magnitudes on either cross-domain projection.
    /// - witness: `horn::tests::offset_arithmetic_covers_zero_equality_and_ceiling`
    #[spec(ensures: |ret| ret.0 == self.0)]
    #[inline]
    #[must_use]
    pub const fn shift_from_zero(self) -> HornShift
    {
        HornShift(self.0)
    }
}

impl From<u128> for HornOffset
{
    /// Wraps a raw natural as an atom offset.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(offset: u128) -> Self
    {
        Self(offset)
    }
}

impl From<HornOffset> for u128
{
    /// Unwraps an atom offset to its raw natural.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(offset: HornOffset) -> Self
    {
        offset.0
    }
}

impl From<LevelOffset> for HornOffset
{
    /// Reads a level atom's offset in the compiled system's offset domain.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(offset: LevelOffset) -> Self
    {
        Self(u128::from(offset))
    }
}

impl From<LevelConstant> for HornOffset
{
    /// Reads a level constant as the offset its bottom atom carries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(constant: LevelConstant) -> Self
    {
        Self(u128::from(constant))
    }
}

/// An upward shift applied to a represented Horn clause family.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct HornShift(u128);

impl HornShift
{
    /// The zero shift, admitting every instance of a clause family.
    pub const ZERO: Self = Self(0_u128);

    /// The unit shift, the minimum of the query system.
    pub const ONE: Self = Self(1_u128);

    /// The atom offset reached by applying this shift to a zero-offset atom.
    ///
    /// This is the explicit cross-domain projection for loop-witness seeds and
    /// targets, where the theory has already fixed the starting offset at zero.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the offset whose value is this shift, which is the
    ///   offset a zero-offset atom reaches under it.
    /// - provides: the sanctioned crossing from the shift domain into the
    ///   offset domain, named per site rather than opened as a conversion.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, ordinary magnitudes and the u128 ceiling are
    ///   used in shifted addition; exact sums and overflow refusals expose
    ///   altered magnitudes on either cross-domain projection.
    /// - witness: `horn::tests::offset_arithmetic_covers_zero_equality_and_ceiling`
    #[spec(ensures: |ret| ret.0 == self.0)]
    #[inline]
    #[must_use]
    pub const fn offset_from_zero(self) -> HornOffset
    {
        HornOffset(self.0)
    }
}

impl From<u128> for HornShift
{
    /// Wraps a raw natural as a clause-family shift.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(shift: u128) -> Self
    {
        Self(shift)
    }
}

impl From<HornShift> for u128
{
    /// Unwraps a clause-family shift to its raw natural.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(shift: HornShift) -> Self
    {
        shift.0
    }
}

/// A base-clause index in the documented compilation order.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ClauseIndex(usize);

impl From<usize> for ClauseIndex
{
    /// Wraps a position in the compilation order as a clause index.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: usize) -> Self
    {
        Self(index)
    }
}

impl From<ClauseIndex> for usize
{
    /// Unwraps a clause index to its raw position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(index: ClauseIndex) -> Self
    {
        index.0
    }
}

impl fmt::Display for ClauseIndex
{
    /// Renders the index as its decimal position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        usize::from(*self).fmt(f)
    }
}

/// The maximum gain of a shifted Horn clause system.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct MaxGain(u128);

impl MaxGain
{
    /// The zero gain, taken by a system with no clauses.
    pub const ZERO: Self = Self(0_u128);
}

impl From<u128> for MaxGain
{
    /// Wraps a raw natural as a system's maximum gain.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(gain: u128) -> Self
    {
        Self(gain)
    }
}

impl From<MaxGain> for u128
{
    /// Unwraps a maximum gain to its raw natural.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(gain: MaxGain) -> Self
    {
        gain.0
    }
}

/// A small-model saturation bound.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct SaturationBound(u128);

impl From<u128> for SaturationBound
{
    /// Wraps a raw natural as a saturation bound.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bound: u128) -> Self
    {
        Self(bound)
    }
}

impl From<SaturationBound> for u128
{
    /// Unwraps a saturation bound to its raw natural.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bound: SaturationBound) -> Self
    {
        bound.0
    }
}

/// A finite round limit for derivation extraction.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct DerivationRoundLimit(u128);

impl From<u128> for DerivationRoundLimit
{
    /// Wraps a raw natural as an extraction round limit.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(limit: u128) -> Self
    {
        Self(limit)
    }
}

impl From<DerivationRoundLimit> for u128
{
    /// Unwraps an extraction round limit to its raw natural.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(limit: DerivationRoundLimit) -> Self
    {
        limit.0
    }
}

/// Whether a model value is infinite.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ModelIsInfinite(bool);

impl From<bool> for ModelIsInfinite
{
    /// Wraps a decision about infiniteness as the model-value answer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(is_infinite: bool) -> Self
    {
        Self(is_infinite)
    }
}

impl From<ModelIsInfinite> for bool
{
    /// Unwraps the model-value answer to a plain decision.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(is_infinite: ModelIsInfinite) -> Self
    {
        is_infinite.0
    }
}

/// Whether a stored model value covers a requested Horn atom.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct AtomCoverage(bool);

impl From<bool> for AtomCoverage
{
    /// Wraps a decision about coverage as the atom-coverage answer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(covered: bool) -> Self
    {
        Self(covered)
    }
}

impl From<AtomCoverage> for bool
{
    /// Unwraps the atom-coverage answer to a plain decision.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(covered: AtomCoverage) -> Self
    {
        covered.0
    }
}

/// Whether a clause is self-subsumed.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ClauseTriviality(bool);

impl From<bool> for ClauseTriviality
{
    /// Wraps a decision about self-subsumption as the clause answer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(trivial: bool) -> Self
    {
        Self(trivial)
    }
}

impl From<ClauseTriviality> for bool
{
    /// Unwraps the clause self-subsumption answer to a plain decision.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(trivial: ClauseTriviality) -> Self
    {
        trivial.0
    }
}

/// Whether saturation drove some component out of the finite range.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SaturationDiverged(bool);

impl From<bool> for SaturationDiverged
{
    /// Wraps a decision about divergence as the saturation answer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(diverged: bool) -> Self
    {
        Self(diverged)
    }
}

impl From<SaturationDiverged> for bool
{
    /// Unwraps the saturation divergence answer to a plain decision.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(diverged: SaturationDiverged) -> Self
    {
        diverged.0
    }
}

/// A represented Horn atom `variable + offset`.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct HornAtom
{
    /// The atom's variable.
    variable: HVar,
    /// The atom's offset.
    offset: HornOffset,
}

impl HornAtom
{
    /// Builds a Horn atom from semantic parts.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        variable: HVar,
        offset: HornOffset,
    ) -> Self
    {
        Self { variable, offset }
    }

    /// The atom's variable.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn variable(self) -> HVar
    {
        self.variable
    }

    /// The atom's offset.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn offset(self) -> HornOffset
    {
        self.offset
    }
}

/// One finite firing recorded in a derivation log.
///
/// The concluded atom rides along with the fired instance so that consumers
/// replaying a log need no second lookup into the clause list, which is what
/// keeps prefix extraction free of a resolution failure mode.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FiringLogStep
{
    /// The fired base clause.
    clause: ClauseIndex,
    /// The upward shift used by the fired instance.
    shift: HornShift,
    /// The atom the fired instance concludes.
    concluded: HornAtom,
}

impl FiringLogStep
{
    /// Builds a finite firing-log step.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        clause: ClauseIndex,
        shift: HornShift,
        concluded: HornAtom,
    ) -> Self
    {
        Self {
            clause,
            shift,
            concluded,
        }
    }

    /// The fired base clause.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn clause(self) -> ClauseIndex
    {
        self.clause
    }

    /// The upward shift used by the fired instance.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn shift(self) -> HornShift
    {
        self.shift
    }

    /// The atom the fired instance concludes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn concluded(self) -> HornAtom
    {
        self.concluded
    }
}

/// A Horn-system variable: the pinned bottom generator `⊥` or an ordinary level
/// variable.
///
/// `⊥` carries constants across the constant-free algebra of the loop-checking
/// paper — a level constant `c` becomes the atom `⊥ + c` — and is deliberately
/// unrepresentable in user levels: it exists only inside compiled systems, so
/// no user input can collide with it. `⊥` orders before every variable, which
/// keeps clause and seed enumeration deterministic.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum HVar
{
    /// The pinned bottom generator.
    Bottom,
    /// An ordinary level variable.
    Var(LevelVar),
}

/// A value of the model domain `ℕ^∞`: the downward-closed atom set
/// `{v+k | k ≤ f(v)}` of a variable, represented by its maximum.
///
/// # Specification
/// - ensures: a finite value covers exactly the offsets at most its maximum;
///   infinity covers every representable offset.
/// - executable: none — the data-item expansion does not check construction;
///   the coverage method checks this interpretation when it is observed.
///
/// # Adequacy
/// - hypothesis: L3 — finite boundaries and infinity are observed through
///   membership below, at and above the maximum and at the numeric ceiling,
///   distinguishing a strict bound and a finite interpretation of infinity.
/// - witness: `horn::tests::model_coverage_separates_absence_infinity_and_equality`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ModelValue
{
    /// A finite maximum.
    Finite(HornOffset),
    /// The infinite value: every atom over the variable holds.
    Infinite,
}

impl ModelValue
{
    /// Whether this is the infinite value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn is_infinite(self) -> ModelIsInfinite
    {
        ModelIsInfinite(matches!(self, Self::Infinite))
    }

    /// The finite maximum this value carries.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `Some(maximum)` for a finite value, `None` for the infinite
    ///   value — the documented absence of a finite maximum, not a swallowed
    ///   failure, since the projection cannot fail.
    /// - provides: the finite projection the admission certificate is computed
    ///   from.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a finite boundary and infinity are observed through
    ///   atom coverage and the finite projection; confusing infinity with a
    ///   finite maximum changes the exact membership verdicts.
    /// - witness: `horn::tests::model_coverage_separates_absence_infinity_and_equality`
    #[spec(ensures: |ret| match (self, ret) {
        (Self::Finite(expected), Some(actual)) => actual.0 == expected.0,
        (Self::Infinite, None) => true,
        _ => false,
    })]
    #[inline]
    #[must_use]
    pub const fn as_finite(self) -> Option<HornOffset>
    {
        match self {
            | Self::Finite(value) => Some(value),
            | Self::Infinite => None,
        }
    }

    /// Whether this value covers the atom offset `offset`, that is whether the
    /// atom holds in the downward-closed set the value stands for.
    ///
    /// # Specification
    /// - requires: nothing; adversarial values are admissible, which is the
    ///   validator's reading.
    /// - ensures: answers affirmatively for the infinite value, and otherwise
    ///   exactly when `offset` is at most the finite maximum — the
    ///   downward-closed reading of the model domain.
    /// - provides: the atom membership test saturation and the validators
    ///   share.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — finite offsets below, at and above a model maximum,
    ///   and the largest offset under infinity, distinguish a strict comparison
    ///   or finite treatment of infinity by exact membership answers.
    /// - witness: `horn::tests::model_coverage_separates_absence_infinity_and_equality`
    #[spec(ensures: |ret| bool::from(ret) == match self {
        Self::Finite(value) => offset <= value,
        Self::Infinite => true,
    })]
    #[inline]
    #[must_use]
    pub(crate) fn covers(
        self,
        offset: HornOffset,
    ) -> AtomCoverage
    {
        AtomCoverage(match self {
            | Self::Finite(value) => offset <= value,
            | Self::Infinite => true,
        })
    }
}

/// One base Horn clause `body → head`, standing for the family of its upward
/// shifts at or above the owning system's minimum shift.
///
/// The body is nonempty and canonical: sorted by variable with one maximal
/// offset per variable. A body atom `x + 2` beside `x + 5` is redundant, since
/// the downward-closed model semantics makes the higher atom imply the lower.
///
/// # Specification
/// - ensures: constructor-produced bodies are nonempty, sorted by variable, and
///   retain exactly the maximum input offset of each variable.
/// - executable: none — data-item invariants are not checked on construction by
///   the expansion; the smart constructor owns the executable boundary.
///
/// # Adequacy
/// - hypothesis: L3 — an empty body is refused, while repeated variables with
///   unequal offsets collapse to one maximal atom. Exact body contents expose
///   lost maxima, duplicate retention and unsorted canonicalization.
/// - witness: `horn::tests::clause_bodies_canonicalize`
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HornClause
{
    /// The body atoms, sorted by variable, one maximal offset each.
    body: Vec<HornAtom>,
    /// The conclusion atom.
    head: HornAtom,
}

impl HornClause
{
    /// Builds a canonical clause from raw body atoms and a head.
    ///
    /// # Specification
    /// - requires: nothing; any raw atom bag is admissible.
    /// - ensures: `Some` exactly when the body is nonempty, holding the
    ///   canonicalized body — sorted, deduplicated by maximal offset.
    /// - provides: the only constructor, so a non-canonical clause is
    ///   unrepresentable.
    /// - fails: `None` on an empty body. The clauses of the theory have
    ///   nonempty bodies; an empty-bodied clause would assert an unconditional
    ///   atom, which no constraint compiles to. Every in-crate call site draws
    ///   its body from a constraint side or from a single-variable bottom
    ///   clause, both nonempty by construction, so the rejection is a
    ///   constructor guard rather than a reachable state.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the canonicalization is pinned by the duplicate-body
    ///   case asserting the exact resulting atom list, and the rejection by the
    ///   empty-body case.
    /// - witness: `horn::tests::clause_bodies_canonicalize`
    #[spec(ensures: |ret| ret.is_some() != raw_body.is_empty())]
    pub fn new(
        raw_body: &[HornAtom],
        head: HornAtom,
    ) -> Option<Self>
    {
        if raw_body.is_empty() {
            return None;
        }
        let mut merged: BTreeMap<HVar, HornOffset> = BTreeMap::new();
        for &atom in raw_body {
            let variable = atom.variable();
            let offset = atom.offset();
            let maximum = merged.entry(variable).or_insert(offset);
            *maximum = (*maximum).max(offset);
        }
        let body = merged
            .into_iter()
            .map(|(variable, offset)| HornAtom::new(variable, offset))
            .collect();
        Some(Self { body, head })
    }

    /// Whether the clause is self-subsumed: some body atom over the head
    /// variable already dominates the conclusion, so every model satisfies the
    /// whole shift family vacuously. Compilation omits such clauses.
    ///
    /// # Specification
    /// - requires: nothing beyond the canonical body the constructor
    ///   guarantees.
    /// - ensures: answers affirmatively exactly when some body atom over the
    ///   head variable carries an offset at or above the head's.
    /// - provides: the omission test the documented compilation applies, so a
    ///   vacuous clause never enters a system.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a different head variable and same-variable heads
    ///   below, at and above the body offset distinguish lost variable
    ///   matching, wrong comparison direction and an exclusive equality
    ///   boundary.
    /// - witness: `horn::tests::clause_gain_and_subsumption_use_the_correct_extrema`
    #[spec(ensures: |ret| bool::from(ret) == self.body.iter().any(|atom|
        atom.variable() == self.head.variable() && atom.offset() >= self.head.offset()))]
    pub fn is_trivial(&self) -> ClauseTriviality
    {
        let head = self.head;
        ClauseTriviality::from(
            self.body
                .iter()
                .any(|&atom| atom.variable() == head.variable() && atom.offset() >= head.offset()),
        )
    }

    /// The body atoms, sorted by variable.
    ///
    /// # Specification
    /// trivial.
    pub fn body(&self) -> &[HornAtom]
    {
        &self.body
    }

    /// The conclusion atom.
    ///
    /// # Specification
    /// trivial.
    pub const fn head(&self) -> HornAtom
    {
        self.head
    }

    /// The clause's gain floored at zero: the conclusion offset minus the
    /// minimal body offset. The system-wide maximum of these is the engine's
    /// growth modulus.
    ///
    /// # Specification
    /// - requires: nothing beyond the nonempty body the constructor guarantees.
    /// - ensures: returns the conclusion offset less the least body offset,
    ///   floored at zero.
    /// - provides: the per-clause growth measure the system's modulus is the
    ///   maximum of.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a two-offset body and heads below, equal to and above
    ///   its minimum distinguish choosing the maximum, reversing subtraction
    ///   and losing the zero floor through exact growth values.
    /// - witness: `horn::tests::clause_gain_and_subsumption_use_the_correct_extrema`
    #[spec(ensures: |ret| u128::from(ret) == self.body.iter().map(|atom|
        u128::from(self.head.offset()).saturating_sub(u128::from(atom.offset())))
        .max().unwrap_or(0))]
    fn gain(&self) -> MaxGain
    {
        let min_body = self
            .body
            .iter()
            .map(|atom| atom.offset())
            .min()
            .unwrap_or(HornOffset::ZERO);
        MaxGain::from(u128::from(self.head.offset().saturating_sub(min_body)))
    }
}

/// A compiled clause system: base clauses plus the minimum admissible upward
/// shift — zero for the admission system, one for the query system of the
/// lemma 2.1 transformation.
#[derive(Clone, Debug)]
pub struct ClauseSystem
{
    /// The base clauses, in the documented deterministic compilation order.
    pub clauses: Vec<HornClause>,
    /// The minimum admissible upward shift.
    pub min_shift: HornShift,
}

impl ClauseSystem
{
    /// The system's maximum gain: the smallest non-negative bound on every
    /// clause's gain. It is shift-invariant, so it is computed once on the base
    /// clauses.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the largest gain over the base clauses, and zero for
    ///   a system with no clauses.
    /// - provides: the growth modulus the saturation bound is computed from.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — empty and nonempty systems separate the zero identity
    ///   from a positive maximum. The paper fixpoint with unequal clause gains
    ///   exposes choosing a smaller gain through the exact finite model.
    /// - witness: `horn::tests::clause_gain_and_subsumption_use_the_correct_extrema`
    /// - witness: `horn::tests::paper_example_reaches_the_published_fixpoint`
    #[spec(ensures: |ret| ret == self.clauses.iter().map(HornClause::gain)
        .max().unwrap_or(MaxGain::ZERO))]
    pub fn maxgain(&self) -> MaxGain
    {
        self.clauses
            .iter()
            .map(HornClause::gain)
            .max()
            .unwrap_or(MaxGain::ZERO)
    }

    /// The maximal body offset over all base clauses, which seeds the loop
    /// check.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the largest offset over every body atom of every base
    ///   clause, and zero for a system with no clauses.
    /// - provides: the offset the loop check seeds its model at.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the empty system and a clause with unequal body
    ///   offsets distinguish a nonzero empty value or a minimum in place of the
    ///   maximum by exact offsets; the paper loop adds multiple-clause
    ///   coverage.
    /// - witness: `horn::tests::clause_gain_and_subsumption_use_the_correct_extrema`
    /// - witness: `horn::tests::paper_loop_variant_diverges_everywhere`
    #[spec(ensures: |ret| ret == self.clauses.iter().flat_map(|clause|
        clause.body().iter().map(|atom| atom.offset())).max().unwrap_or(HornOffset::ZERO))]
    pub fn max_body_offset(&self) -> HornOffset
    {
        self.clauses
            .iter()
            .flat_map(|clause| clause.body().iter().map(|atom| atom.offset()))
            .max()
            .unwrap_or(HornOffset::ZERO)
    }
}

/// The strongest conclusion a clause family forces from a model, per [`fire`].
///
/// # Specification
/// - ensures: results produced by firing contain a finite shift exactly for a
///   finite forced value; the shift is maximal among enabled instances.
/// - executable: none — maximality depends on the external clause and model;
///   the firing function checks that relation at the production boundary.
///
/// # Adequacy
/// - hypothesis: L3 — finite, mixed and all-infinite bodies are observed by the
///   exact conclusion and optional shift. Missing variables, insufficient
///   offsets and the minimum-shift boundary expose invalid firing admission.
/// - witness: `horn::tests::firing_requires_the_minimum_shift`
/// - witness: `horn::tests::firing_skips_absent_and_dominated_bodies`
/// - witness: `horn::tests::mixed_finite_bodies_bound_the_shift`
/// - witness: `horn::tests::infinite_bodies_force_infinite_conclusions`
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Firing
{
    /// The forced value of the head variable.
    pub value: ModelValue,
    /// The shift the strongest instance fires at. It is `None` exactly when
    /// every body variable is infinite, where the conclusion is infinite with
    /// no single witnessing instance — a documented absence, not a swallowed
    /// failure.
    pub shift: Option<HornShift>,
}

/// The result of [`saturate`]: the least model, the finite-shift firing log,
/// and whether any component left the finite range.
///
/// # Specification
/// - ensures: results produced by saturation contain the least model above the
///   seed, its finite updates in application order and its divergence.
/// - executable: none — leastness quantifies over models of the external clause
///   system, and the initial seed is no longer retained in this value.
///
/// # Adequacy
/// - hypothesis: L1 — the published example fixes each finite model value and
///   its loop variant fixes the infinite components. L2 — the empty-system
///   differential covers unconstrained queries, exposing incorrect propagation
///   or a finite/infinite misclassification.
/// - witness: `horn::tests::paper_example_reaches_the_published_fixpoint`
/// - witness: `horn::tests::paper_loop_variant_diverges_everywhere`
/// - witness: `entailment_oracle::entailment_oracle::prop_empty_poset_agrees_with_the_free_oracle`
#[derive(Clone, Debug)]
pub struct Saturation
{
    /// The least model above the seed.
    pub values: BTreeMap<HVar, ModelValue>,
    /// Every applied finite-shift firing, in application order.
    /// Infinite-conclusion firings, where all body variables are infinite, are
    /// not logged: they have no single replayable instance and occur only after
    /// divergence is already recorded.
    pub log: Vec<FiringLogStep>,
    /// Whether some component was driven past the small-model bound, so its
    /// true least-model value is infinite.
    pub diverged: SaturationDiverged,
}

/// The least model of `system` above `seed`, computed by monotone rounds and
/// snapping finite values above `snap_bound` to the infinite value.
///
/// # Specification
/// - requires: `snap_bound` is a small-model bound for `seed` — at least the
///   largest finite seed value plus the variable count times the system's
///   maximum gain — so that a value driven past it can only belong to an
///   infinite component of the true least model.
/// - ensures: the returned values are the least model of the system's shift
///   families above `seed`, with predecessor clauses implicit in the
///   downward-closed representation; divergence holds exactly when some
///   component is infinite; the log replays every finite-shift update in order.
/// - provides: the shared model engine of poset admission and entailment.
///   Leastness quantifies over all models; the finite update log is not a
///   leastness certificate. The postcondition stays prose rather than being
///   weakened to fixed-point or divergence checks. The consumed seed would also
///   need an owned snapshot, evaluated even without runtime checks.
/// - fails: [`LevelError::Overflow`] only through [`fire`] on adversarial
///   inputs; engine-internal values stay at most `snap_bound` plus the maximum
///   gain.
/// - panics: none.
/// - intension: the loop runs to a fixed point over an explicit worklist of
///   rounds, never recursively. Values are monotone per variable, bounded by
///   `snap_bound` while finite, and cross into the infinite value at most once
///   per variable, so every round without progress is final and only finitely
///   many rounds make progress.
///
/// # Errors
/// [`LevelError::Overflow`] — a firing's conclusion passed the `u128` range.
///
/// # Adequacy
/// - hypothesis: L1 — the paper example fixes the finite model and its loop
///   variant fixes the divergent components. L2 — unconstrained queries agree
///   with the free oracle. L3 — a zero-gain conclusion exactly at the bound
///   remains finite, while a unit-gain loop records the updates at and just
///   above its bound; exact models and logs expose early or late snapping.
/// - witness: `horn::tests::saturation_snaps_only_above_the_bound`
/// - witness: `horn::tests::paper_example_reaches_the_published_fixpoint`
/// - witness: `horn::tests::paper_loop_variant_diverges_everywhere`
/// - witness: `entailment_oracle::entailment_oracle::prop_empty_poset_agrees_with_the_free_oracle`
#[spec(requires: {
    let variables: alloc::collections::BTreeSet<_> = seed.keys().copied()
        .chain(system.clauses.iter().flat_map(|clause| {
            clause.body().iter().map(|atom| atom.variable())
                .chain(core::iter::once(clause.head().variable()))
        })).collect();
    let ceiling = seed.values().filter_map(|value| value.as_finite())
        .map(u128::from).max().unwrap_or(0);
    u128::try_from(variables.len()).ok()
        .and_then(|count| count.checked_mul(u128::from(system.maxgain())))
        .and_then(|gain| ceiling.checked_add(gain))
        .is_some_and(|bound| bound <= u128::from(snap_bound))
})]
pub fn saturate(
    system: &ClauseSystem,
    seed: BTreeMap<HVar, ModelValue>,
    snap_bound: SaturationBound,
) -> Result<Saturation, LevelError>
{
    let mut values = seed;
    let mut log = Vec::new();
    let mut diverged = false;
    loop {
        let mut progress = false;
        for (index, clause) in system.clauses.iter().enumerate() {
            let firing = fire(clause, &values, system.min_shift)?;
            let Some(firing) = firing
            else {
                continue;
            };
            let head = clause.head();
            let head_var = head.variable();
            let current = values.get(&head_var).copied();
            let snapped = matches!(
                firing.value,
                ModelValue::Finite(value) if u128::from(value) > u128::from(snap_bound)
            );
            let candidate = if snapped {
                ModelValue::Infinite
            }
            else {
                firing.value
            };
            let improved = match (current, candidate) {
                | (Some(ModelValue::Infinite), _) => false,
                | (None, _) | (Some(ModelValue::Finite(_)), ModelValue::Infinite) => true,
                | (Some(ModelValue::Finite(existing)), ModelValue::Finite(update)) => {
                    update > existing
                },
            };
            if improved {
                if bool::from(candidate.is_infinite()) {
                    diverged = true;
                }
                if let Some(shift) = firing.shift {
                    let concluded_offset = head.offset().checked_add_shift(shift)?;
                    let concluded = HornAtom::new(head_var, concluded_offset);
                    log.push(FiringLogStep::new(
                        ClauseIndex::from(index),
                        shift,
                        concluded,
                    ));
                }
                let _previous = values.insert(head_var, candidate);
                progress = true;
            }
        }
        if !progress {
            break;
        }
    }
    Ok(Saturation {
        values,
        log,
        diverged: SaturationDiverged::from(diverged),
    })
}

/// Instrumented forward reasoning: starting from exactly the `seed` atoms, fire
/// clauses until every target atom is derived, logging each applied step.
///
/// # Specification
/// - requires: every `seed` value is finite — the derivation's body, where
///   variables absent from it have no atoms until derived.
/// - ensures: `Ok(Some(log))` exactly when every target was covered within
///   `round_limit` rounds, with the log replaying to a state covering all
///   targets from the seed; `Ok(None)` when the limit passed first, which the
///   caller treats as the theory-refuting case and surfaces as a typed error
///   rather than trusting it.
/// - provides: the evidence extractor behind loop witnesses, making the pumping
///   claim of corollary 3.5 replayable. The postcondition needs the consumed
///   seed and round history, neither retained by the output. An owned entry
///   snapshot runs even without checks in the pinned expansion; coverage alone
///   would weaken the round-limit and replay claims.
/// - fails: [`LevelError::Overflow`] when a derived value passes the `u128`
///   range, bounded in practice by the round limit times the maximum gain above
///   the seed.
/// - panics: none.
/// - intension: rounds are an explicit counter over an iterative loop, never
///   recursion; at most `round_limit` rounds run, each over finitely many
///   clauses, with early exit as soon as coverage is reached.
///
/// # Errors
/// [`LevelError::Overflow`] — a derived value passed the `u128` range.
///
/// # Adequacy
/// - hypothesis: L2 — paper loop fixtures replay through the independent
///   witness validator. L3 — empty and seed-covered targets with no rounds, and
///   a two-step target at limits zero, one and two distinguish an early cutoff
///   or an extra round by exact optional logs and concluded atoms.
/// - witness: `horn::tests::derivation_respects_zero_and_exact_round_limits`
/// - witness: `horn::tests::derive_targets_extracts_a_checkable_log`
/// - witness: `poset::tests::paper_loop_variant_returns_a_validating_loop_witness`
/// - witness: `poset::tests::self_successor_equality_loops`
#[spec(requires: seed.values().all(|value| matches!(*value, ModelValue::Finite(_))))]
pub fn derive_targets(
    system: &ClauseSystem,
    seed: BTreeMap<HVar, ModelValue>,
    targets: &[HornAtom],
    round_limit: DerivationRoundLimit,
) -> Result<Option<Vec<FiringLogStep>>, LevelError>
{
    let mut values = seed;
    let mut log = Vec::new();
    if bool::from(covered(&values, targets)) {
        return Ok(Some(log));
    }
    let mut round = 0_u128;
    while round < u128::from(round_limit) {
        let mut progress = false;
        for (index, clause) in system.clauses.iter().enumerate() {
            let firing = fire(clause, &values, system.min_shift)?;
            let Some(firing) = firing
            else {
                continue;
            };
            let Some(shift) = firing.shift
            else {
                continue;
            };
            let head = clause.head();
            let head_var = head.variable();
            let current = values.get(&head_var).copied();
            let improved = match (current, firing.value) {
                | (Some(ModelValue::Infinite), _) => false,
                | (None, _) | (Some(ModelValue::Finite(_)), ModelValue::Infinite) => true,
                | (Some(ModelValue::Finite(existing)), ModelValue::Finite(update)) => {
                    update > existing
                },
            };
            if improved {
                let _previous = values.insert(head_var, firing.value);
                let concluded_offset = head.offset().checked_add_shift(shift)?;
                let concluded = HornAtom::new(head_var, concluded_offset);
                log.push(FiringLogStep::new(
                    ClauseIndex::from(index),
                    shift,
                    concluded,
                ));
                progress = true;
                if bool::from(covered(&values, targets)) {
                    return Ok(Some(log));
                }
            }
        }
        if !progress {
            break;
        }
        round = round.checked_add(1_u128).ok_or(LevelError::Overflow)?;
    }
    Ok(None)
}

/// Whether every target atom holds in `values`.
///
/// # Specification
/// - requires: nothing; `values` may be partial, where an absent variable
///   carries no atoms.
/// - ensures: answers affirmatively exactly when the model value over each
///   target's variable covers that target, so an empty target list is covered.
/// - provides: the stopping test derivation extraction polls after every
///   firing.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — empty targets, an absent variable, offsets at and above a
///   finite maximum, infinity and a mixed covered/uncovered target list
///   distinguish default presence, strictness and existential in place of
///   universal coverage by exact verdicts.
/// - witness: `horn::tests::model_coverage_separates_absence_infinity_and_equality`
#[spec(ensures: |ret| bool::from(ret) == targets.iter().all(|target|
    values.get(&target.variable()).is_some_and(|value| bool::from(value.covers(target.offset())))))]
pub fn covered(
    values: &BTreeMap<HVar, ModelValue>,
    targets: &[HornAtom],
) -> AtomCoverage
{
    AtomCoverage::from(targets.iter().all(|&target| {
        values
            .get(&target.variable())
            .is_some_and(|value| bool::from(value.covers(target.offset())))
    }))
}

/// The firing rule: what the whole shift family of `clause`, at shifts at or
/// above `min_shift`, forces from `model`.
///
/// # Specification
/// - requires: nothing. `model` may be partial, where an absent variable has no
///   atoms, and may hold adversarial values, which is the validator's reading.
/// - ensures: `Ok(None)` when no admissible instance's body is satisfied — an
///   absent body variable, a finite maximum below a body offset, or a maximal
///   admissible shift below `min_shift`; `Ok(Some(firing))` with the maximal
///   forced conclusion otherwise, that is `head + k₀` at the maximal admissible
///   shift `k₀ = min(model(xᵢ) − kᵢ)` over the finite body variables, or the
///   infinite value when every body variable is infinite.
/// - provides: the single firing rule shared by saturation, derivation, and the
///   countermodel validator.
/// - fails: [`LevelError::Overflow`] when `head + k₀` passes the `u128` range —
///   unreachable for engine-bounded models, reachable for adversarial validator
///   inputs, which are rejected rather than wrapped.
/// - panics: none.
///
/// # Errors
/// [`LevelError::Overflow`] — the forced conclusion passed the `u128` range.
///
/// # Adequacy
/// - hypothesis: L3 — each guard arm is pinned by an exact unit case, and the
///   rule as a whole is exercised by the paper-example golden and the
///   differential property suite, since a firing mutant shifts the computed
///   fixpoint away from the published one or breaks free-fragment agreement.
/// - witness: `horn::tests::firing_at_the_ceiling_refuses_only_overflow`
/// - witness: `horn::tests::firing_requires_the_minimum_shift`
/// - witness: `horn::tests::firing_skips_absent_and_dominated_bodies`
/// - witness: `horn::tests::infinite_bodies_force_infinite_conclusions`
/// - witness: `horn::tests::mixed_finite_bodies_bound_the_shift`
/// - witness: `horn::tests::paper_example_reaches_the_published_fixpoint`
#[spec(ensures: |ret| {
    let enabled = clause.body().iter().all(|atom| {
        model.get(&atom.variable()).is_some_and(|value| bool::from(value.covers(atom.offset())))
    });
    let shift = clause.body().iter().filter_map(|atom| {
        let maximum = model.get(&atom.variable()).and_then(|value| value.as_finite())?;
        u128::from(maximum).checked_sub(u128::from(atom.offset()))
    }).min().map(HornShift::from);
    let enabled = enabled && shift.is_none_or(|shift| shift >= min_shift);
    ret.as_ref().is_err() || ret.as_ref().is_ok_and(|firing| {
        firing.as_ref().map_or_else(|| !enabled, |firing| {
            enabled && firing.shift == shift && shift.map_or_else(
                || firing.value == ModelValue::Infinite,
                |shift| u128::from(clause.head().offset()).checked_add(u128::from(shift))
                    .is_some_and(|value| firing.value == ModelValue::Finite(HornOffset::from(value))),
            )
        })
    })
})]
pub fn fire(
    clause: &HornClause,
    model: &BTreeMap<HVar, ModelValue>,
    min_shift: HornShift,
) -> Result<Option<Firing>, LevelError>
{
    let mut max_shift: Option<HornShift> = None;
    let mut all_infinite = true;
    for &atom in clause.body() {
        match model.get(&atom.variable()) {
            | None => return Ok(None),
            | Some(&ModelValue::Infinite) => {},
            | Some(&ModelValue::Finite(maximum)) => {
                all_infinite = false;
                let headroom = u128::from(maximum).checked_sub(u128::from(atom.offset()));
                let Some(cap) = headroom
                else {
                    return Ok(None);
                };
                let cap = HornShift::from(cap);
                max_shift = Some(max_shift.map_or(cap, |current| current.min(cap)));
            },
        }
    }
    if all_infinite {
        return Ok(Some(Firing {
            value: ModelValue::Infinite,
            shift: None,
        }));
    }
    let Some(shift) = max_shift
    else {
        return Ok(None);
    };
    if shift < min_shift {
        return Ok(None);
    }
    let head = clause.head();
    let value = head.offset().checked_add_shift(shift)?;
    Ok(Some(Firing {
        value: ModelValue::Finite(value),
        shift: Some(shift),
    }))
}

#[cfg(test)]
mod tests
{
    use alloc::collections::BTreeMap;
    use alloc::vec;
    use alloc::vec::Vec;

    use anodized::spec;

    use super::ClauseIndex;
    use super::ClauseSystem;
    use super::DerivationRoundLimit;
    use super::HVar;
    use super::HornAtom;
    use super::HornClause;
    use super::HornOffset;
    use super::HornShift;
    use super::MaxGain;
    use super::ModelValue;
    use super::SaturationBound;
    use super::derive_targets;
    use super::fire;
    use super::saturate;
    use crate::level::LevelVar;
    use crate::level::LevelVarIndex;

    #[test]
    fn saturation_snaps_only_above_the_bound()
    {
        let finite = ClauseSystem {
            clauses: vec![
                HornClause::new(
                    &[HornAtom::new(v0(), HornOffset::ZERO)],
                    HornAtom::new(v1(), HornOffset::ZERO),
                )
                .expect("nonempty body"),
            ],
            min_shift: HornShift::ZERO,
        };
        let seed = BTreeMap::from([(v0(), ModelValue::Finite(HornOffset::ZERO))]);
        let fixed = saturate(&finite, seed.clone(), SaturationBound::from(0_u128))
            .expect("zero-gain model");
        assert_eq!(
            fixed.values,
            BTreeMap::from([
                (v0(), ModelValue::Finite(HornOffset::ZERO)),
                (v1(), ModelValue::Finite(HornOffset::ZERO)),
            ])
        );
        assert!(!bool::from(fixed.diverged));
        let looping = ClauseSystem {
            clauses: vec![
                HornClause::new(
                    &[HornAtom::new(v0(), HornOffset::ZERO)],
                    HornAtom::new(v0(), HornOffset::ONE),
                )
                .expect("nonempty body"),
            ],
            min_shift: HornShift::ZERO,
        };
        let fixed = saturate(&looping, seed, SaturationBound::from(1_u128))
            .expect("bounded loop detection");
        assert_eq!(fixed.values, BTreeMap::from([(v0(), ModelValue::Infinite)]));
        assert!(bool::from(fixed.diverged));
        assert_eq!(
            fixed
                .log
                .iter()
                .map(|step| (step.shift(), step.concluded()))
                .collect::<Vec<_>>(),
            vec![
                (HornShift::ZERO, HornAtom::new(v0(), HornOffset::ONE)),
                (
                    HornShift::ONE,
                    HornAtom::new(v0(), HornOffset::from(2_u128))
                ),
            ]
        );
    }

    #[test]
    fn offset_arithmetic_covers_zero_equality_and_ceiling()
    {
        for (left, right, expected) in [
            (0_u128, 0_u128, Ok(0_u128)),
            (7, 3, Ok(10)),
            (u128::MAX, 0, Ok(u128::MAX)),
            (u128::MAX.saturating_sub(1), 1, Ok(u128::MAX)),
            (u128::MAX, 1, Err(crate::level::LevelError::Overflow)),
        ] {
            let offset = HornOffset::from(left);
            let shift = HornOffset::from(right).shift_from_zero();
            assert_eq!(
                offset.checked_add(HornOffset::from(right)).map(u128::from),
                expected
            );
            assert_eq!(offset.checked_add_shift(shift).map(u128::from), expected);
            assert_eq!(
                offset.checked_add(shift.offset_from_zero()).map(u128::from),
                expected
            );
        }
        for (left, right, expected) in [(2_u128, 1_u128, 1_u128), (2, 2, 0), (2, 3, 0)] {
            assert_eq!(
                HornOffset::from(left).saturating_sub(HornOffset::from(right)),
                HornOffset::from(expected)
            );
        }
    }

    #[test]
    fn model_coverage_separates_absence_infinity_and_equality()
    {
        let finite = ModelValue::Finite(HornOffset::from(2_u128));
        assert_eq!(finite.as_finite(), Some(HornOffset::from(2_u128)));
        assert_eq!(ModelValue::Infinite.as_finite(), None);
        let values = BTreeMap::from([(v0(), finite), (v1(), ModelValue::Infinite)]);
        for (offset, expected) in [(1_u128, true), (2, true), (3, false)] {
            let offset = HornOffset::from(offset);
            assert_eq!(bool::from(finite.covers(offset)), expected);
            assert_eq!(
                bool::from(super::covered(&values, &[HornAtom::new(v0(), offset)])),
                expected
            );
        }
        let largest = HornOffset::from(u128::MAX);
        assert!(bool::from(ModelValue::Infinite.covers(largest)));
        assert!(bool::from(super::covered(&values, &[HornAtom::new(
            v1(),
            largest
        )])));
        assert!(!bool::from(super::covered(&values, &[HornAtom::new(
            v2(),
            HornOffset::ZERO
        )])));
        assert!(bool::from(super::covered(&BTreeMap::new(), &[])));
        assert!(!bool::from(super::covered(&values, &[
            HornAtom::new(v1(), largest),
            HornAtom::new(v0(), HornOffset::from(3_u128))
        ])));
    }

    #[test]
    fn clause_gain_and_subsumption_use_the_correct_extrema()
    {
        let empty = ClauseSystem {
            clauses: vec![],
            min_shift: HornShift::ZERO,
        };
        assert_eq!(empty.maxgain(), MaxGain::ZERO);
        assert_eq!(empty.max_body_offset(), HornOffset::ZERO);
        let body = [
            HornAtom::new(v0(), HornOffset::from(2_u128)),
            HornAtom::new(v1(), HornOffset::from(5_u128)),
        ];
        let clause = HornClause::new(&body, HornAtom::new(v2(), HornOffset::from(7_u128)))
            .expect("nonempty body");
        assert_eq!(clause.gain(), MaxGain::from(5_u128));
        assert!(!bool::from(clause.is_trivial()));
        let system = ClauseSystem {
            clauses: vec![clause],
            min_shift: HornShift::ONE,
        };
        assert_eq!(system.maxgain(), MaxGain::from(5_u128));
        assert_eq!(system.max_body_offset(), HornOffset::from(5_u128));
        for (head, expected) in [(1_u128, true), (2, true), (3, false)] {
            let clause = HornClause::new(&body, HornAtom::new(v0(), HornOffset::from(head)))
                .expect("nonempty body");
            assert_eq!(bool::from(clause.is_trivial()), expected);
            assert_eq!(clause.gain(), MaxGain::from(head.saturating_sub(2)));
        }
    }

    #[test]
    fn derivation_respects_zero_and_exact_round_limits()
    {
        let system = ClauseSystem {
            clauses: vec![
                HornClause::new(
                    &[HornAtom::new(v0(), HornOffset::ZERO)],
                    HornAtom::new(v0(), HornOffset::ONE),
                )
                .expect("nonempty body"),
            ],
            min_shift: HornShift::ZERO,
        };
        let seed = BTreeMap::from([(v0(), ModelValue::Finite(HornOffset::ZERO))]);
        for targets in [vec![], vec![HornAtom::new(v0(), HornOffset::ZERO)]] {
            assert_eq!(
                derive_targets(
                    &system,
                    seed.clone(),
                    &targets,
                    DerivationRoundLimit::from(0_u128)
                ),
                Ok(Some(vec![]))
            );
        }
        let targets = [HornAtom::new(v0(), HornOffset::from(2_u128))];
        for limit in [0_u128, 1] {
            assert_eq!(
                derive_targets(
                    &system,
                    seed.clone(),
                    &targets,
                    DerivationRoundLimit::from(limit)
                ),
                Ok(None)
            );
        }
        let log = derive_targets(&system, seed, &targets, DerivationRoundLimit::from(2_u128))
            .expect("finite derivation")
            .expect("two rounds cover the goal");
        assert_eq!(
            log.iter()
                .map(|step| (step.clause(), step.shift(), step.concluded()))
                .collect::<Vec<_>>(),
            vec![
                (
                    ClauseIndex::from(0_usize),
                    HornShift::ZERO,
                    HornAtom::new(v0(), HornOffset::ONE)
                ),
                (
                    ClauseIndex::from(0_usize),
                    HornShift::ONE,
                    HornAtom::new(v0(), HornOffset::from(2_u128))
                ),
            ]
        );
    }

    #[test]
    fn firing_at_the_ceiling_refuses_only_overflow()
    {
        let clause = HornClause::new(
            &[HornAtom::new(v0(), HornOffset::ZERO)],
            HornAtom::new(v1(), HornOffset::ONE),
        )
        .expect("nonempty body");
        let model = BTreeMap::from([(v0(), ModelValue::Finite(HornOffset::from(u128::MAX)))]);
        assert_eq!(
            fire(&clause, &model, HornShift::ZERO),
            Err(crate::level::LevelError::Overflow)
        );
        let model = BTreeMap::from([(
            v0(),
            ModelValue::Finite(HornOffset::from(u128::MAX.saturating_sub(1))),
        )]);
        let firing = fire(&clause, &model, HornShift::ZERO)
            .expect("exact ceiling")
            .expect("enabled body");
        assert_eq!(
            firing.value,
            ModelValue::Finite(HornOffset::from(u128::MAX))
        );
        assert_eq!(
            firing.shift,
            Some(HornShift::from(u128::MAX.saturating_sub(1)))
        );
    }

    #[test]
    fn paper_example_reaches_the_published_fixpoint()
    {
        let system = ClauseSystem {
            clauses: paper_clauses(),
            min_shift: HornShift::ZERO,
        };
        assert_eq!(
            MaxGain::from(3_u128),
            system.maxgain(),
            "the worked example reports a maximum gain of 3"
        );
        let bound = SaturationBound::from(15_u128);
        let outcome = saturate(&system, zero_seed(), bound).expect("the base example saturates");
        assert!(
            !bool::from(outcome.diverged),
            "the base example has a finite model"
        );
        let expected: BTreeMap<HVar, ModelValue> = [
            (v0(), ModelValue::Finite(HornOffset::from(0_u128))),
            (v1(), ModelValue::Finite(HornOffset::from(1_u128))),
            (v2(), ModelValue::Finite(HornOffset::from(4_u128))),
            (v3(), ModelValue::Finite(HornOffset::from(3_u128))),
            (v4(), ModelValue::Finite(HornOffset::from(1_u128))),
        ]
        .into_iter()
        .collect();
        assert_eq!(
            outcome.values, expected,
            "the minimal model above zero is 01431 in the order a, b, c, d, e"
        );
    }

    #[test]
    fn paper_loop_variant_diverges_everywhere()
    {
        let mut clauses = paper_clauses();
        clauses.push(
            HornClause::new(
                &[HornAtom::new(v4(), HornOffset::from(0_u128))],
                HornAtom::new(v0(), HornOffset::from(0_u128)),
            )
            .expect("a single-atom body is nonempty"),
        );
        let system = ClauseSystem {
            clauses,
            min_shift: HornShift::ZERO,
        };
        let bound = SaturationBound::from(15_u128);
        let outcome = saturate(&system, zero_seed(), bound).expect("the loop variant saturates");
        assert!(
            bool::from(outcome.diverged),
            "adding e implies a creates a loop"
        );
        for variable in [v0(), v1(), v2(), v3(), v4()] {
            assert_eq!(
                Some(&ModelValue::Infinite),
                outcome.values.get(&variable),
                "every variable diverges in the loop variant"
            );
        }
    }

    #[test]
    fn firing_requires_the_minimum_shift()
    {
        let clause = HornClause::new(
            &[HornAtom::new(v0(), HornOffset::from(0_u128))],
            HornAtom::new(v1(), HornOffset::from(0_u128)),
        )
        .expect("a single-atom body is nonempty");
        let model: BTreeMap<HVar, ModelValue> =
            core::iter::once((v0(), ModelValue::Finite(HornOffset::from(0_u128)))).collect();
        let at_zero = fire(&clause, &model, HornShift::ZERO).expect("firing does not overflow");
        assert!(
            at_zero.is_some(),
            "shift 0 is admissible at minimum shift 0"
        );
        let at_one = fire(&clause, &model, HornShift::ONE).expect("firing does not overflow");
        assert!(
            at_one.is_none(),
            "shift 0 is inadmissible at minimum shift 1"
        );
    }

    #[test]
    fn firing_skips_absent_and_dominated_bodies()
    {
        let clause = HornClause::new(
            &[HornAtom::new(v0(), HornOffset::from(2_u128))],
            HornAtom::new(v1(), HornOffset::from(0_u128)),
        )
        .expect("a single-atom body is nonempty");
        let absent: BTreeMap<HVar, ModelValue> = BTreeMap::new();
        assert!(
            fire(&clause, &absent, HornShift::ZERO)
                .expect("firing does not overflow")
                .is_none(),
            "an absent body variable blocks every instance"
        );
        let below: BTreeMap<HVar, ModelValue> =
            core::iter::once((v0(), ModelValue::Finite(HornOffset::from(1_u128)))).collect();
        assert!(
            fire(&clause, &below, HornShift::ZERO)
                .expect("firing does not overflow")
                .is_none(),
            "a maximum below the body offset blocks every instance"
        );
    }

    #[test]
    fn infinite_bodies_force_infinite_conclusions()
    {
        let clause = HornClause::new(
            &[HornAtom::new(v0(), HornOffset::from(3_u128))],
            HornAtom::new(v1(), HornOffset::from(0_u128)),
        )
        .expect("a single-atom body is nonempty");
        let model: BTreeMap<HVar, ModelValue> =
            core::iter::once((v0(), ModelValue::Infinite)).collect();
        let firing = fire(&clause, &model, HornShift::ZERO)
            .expect("firing does not overflow")
            .expect("an infinite body fires");
        assert_eq!(
            ModelValue::Infinite,
            firing.value,
            "an all-infinite body forces an infinite conclusion"
        );
        assert_eq!(None, firing.shift, "no single instance witnesses it");
    }

    #[test]
    fn mixed_finite_bodies_bound_the_shift()
    {
        let clause = HornClause::new(
            &[
                HornAtom::new(v0(), HornOffset::from(0_u128)),
                HornAtom::new(v1(), HornOffset::from(2_u128)),
            ],
            HornAtom::new(v2(), HornOffset::from(1_u128)),
        )
        .expect("a two-atom body is nonempty");
        let model: BTreeMap<HVar, ModelValue> = [
            (v0(), ModelValue::Infinite),
            (v1(), ModelValue::Finite(HornOffset::from(5_u128))),
        ]
        .into_iter()
        .collect();
        let firing = fire(&clause, &model, HornShift::ZERO)
            .expect("firing does not overflow")
            .expect("a mixed body fires");
        assert_eq!(
            ModelValue::Finite(HornOffset::from(4_u128)),
            firing.value,
            "the finite body variable bounds the shift: 5 minus 2 is 3, head 1 plus 3 is 4"
        );
        assert_eq!(Some(HornShift::from(3_u128)), firing.shift);
    }

    #[test]
    fn derive_targets_extracts_a_checkable_log()
    {
        // The self-loop `x implies x+1`: from `x+0`, deriving `x+3` takes three
        // logged pumping steps.
        let clauses = vec![
            HornClause::new(
                &[HornAtom::new(v0(), HornOffset::from(0_u128))],
                HornAtom::new(v0(), HornOffset::from(1_u128)),
            )
            .expect("a single-atom body is nonempty"),
        ];
        let system = ClauseSystem {
            clauses,
            min_shift: HornShift::ZERO,
        };
        let seed: BTreeMap<HVar, ModelValue> =
            core::iter::once((v0(), ModelValue::Finite(HornOffset::from(0_u128)))).collect();
        let targets = [HornAtom::new(v0(), HornOffset::from(3_u128))];
        let log = derive_targets(&system, seed, &targets, DerivationRoundLimit::from(16_u128))
            .expect("derivation does not overflow")
            .expect("the target is derivable");
        let steps: Vec<(ClauseIndex, HornShift, HornOffset)> = log
            .iter()
            .map(|step| (step.clause(), step.shift(), step.concluded().offset()))
            .collect();
        assert_eq!(
            steps,
            vec![
                (
                    ClauseIndex::from(0_usize),
                    HornShift::from(0_u128),
                    HornOffset::from(1_u128)
                ),
                (
                    ClauseIndex::from(0_usize),
                    HornShift::from(1_u128),
                    HornOffset::from(2_u128)
                ),
                (
                    ClauseIndex::from(0_usize),
                    HornShift::from(2_u128),
                    HornOffset::from(3_u128)
                ),
            ],
            "each pumping step fires the sole clause at the next shift"
        );
    }

    #[test]
    fn derive_targets_reports_underivable_targets()
    {
        let clauses = vec![
            HornClause::new(
                &[HornAtom::new(v0(), HornOffset::from(0_u128))],
                HornAtom::new(v1(), HornOffset::from(0_u128)),
            )
            .expect("a single-atom body is nonempty"),
        ];
        let system = ClauseSystem {
            clauses,
            min_shift: HornShift::ZERO,
        };
        let seed: BTreeMap<HVar, ModelValue> =
            core::iter::once((v0(), ModelValue::Finite(HornOffset::from(0_u128)))).collect();
        let targets = [HornAtom::new(v1(), HornOffset::from(5_u128))];
        let outcome = derive_targets(&system, seed, &targets, DerivationRoundLimit::from(16_u128))
            .expect("derivation does not overflow");
        assert!(
            outcome.is_none(),
            "a fixpoint below the target reports non-derivability"
        );
    }

    #[test]
    fn trivial_clauses_are_recognized()
    {
        let subsumed = HornClause::new(
            &[HornAtom::new(v0(), HornOffset::from(1_u128))],
            HornAtom::new(v0(), HornOffset::from(0_u128)),
        )
        .expect("a single-atom body is nonempty");
        assert!(
            bool::from(subsumed.is_trivial()),
            "x+1 implies x is self-subsumed"
        );
        let productive = HornClause::new(
            &[HornAtom::new(v0(), HornOffset::from(0_u128))],
            HornAtom::new(v0(), HornOffset::from(1_u128)),
        )
        .expect("a single-atom body is nonempty");
        assert!(
            !bool::from(productive.is_trivial()),
            "x implies x+1 is productive"
        );
    }

    #[test]
    fn clause_bodies_canonicalize()
    {
        let clause = HornClause::new(
            &[
                HornAtom::new(v0(), HornOffset::from(2_u128)),
                HornAtom::new(v0(), HornOffset::from(5_u128)),
                HornAtom::new(v1(), HornOffset::from(0_u128)),
            ],
            HornAtom::new(v2(), HornOffset::from(0_u128)),
        )
        .expect("a three-atom body is nonempty");
        assert_eq!(
            clause.body(),
            &[
                HornAtom::new(v0(), HornOffset::from(5_u128)),
                HornAtom::new(v1(), HornOffset::from(0_u128)),
            ],
            "duplicate body variables keep the maximal offset"
        );
        assert!(
            HornClause::new(&[], HornAtom::new(v0(), HornOffset::from(0_u128))).is_none(),
            "an empty body is unrepresentable"
        );
    }

    /// The worked example's base clauses
    /// `{a,b → b+1; b → c+3; c+1 → d; b,d+2 → e}`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the four base clauses of the worked example, in the
    ///   published order.
    /// - provides: the fixture the engine's tests are stated against.
    /// - panics: when a body is rejected as empty, which the literal nonempty
    ///   bodies here never are.
    ///
    /// # Adequacy
    /// - hypothesis: L1 — the fixed paper example is observed by its published
    ///   finite fixpoint and its all-diverging variant. Changed clause
    ///   directions, omitted variables and offsets cross those finite/infinite
    ///   boundaries.
    /// - witness: `horn::tests::paper_example_reaches_the_published_fixpoint`
    /// - witness: `horn::tests::paper_loop_variant_diverges_everywhere`
    #[spec(ensures: |ret| ret.iter().map(|clause| clause.head().variable())
        .eq([v1(), v2(), v3(), v4()]))]
    fn paper_clauses() -> Vec<HornClause>
    {
        vec![
            HornClause::new(
                &[
                    HornAtom::new(v0(), HornOffset::from(0_u128)),
                    HornAtom::new(v1(), HornOffset::from(0_u128)),
                ],
                HornAtom::new(v1(), HornOffset::from(1_u128)),
            )
            .expect("a two-atom body is nonempty"),
            HornClause::new(
                &[HornAtom::new(v1(), HornOffset::from(0_u128))],
                HornAtom::new(v2(), HornOffset::from(3_u128)),
            )
            .expect("a single-atom body is nonempty"),
            HornClause::new(
                &[HornAtom::new(v2(), HornOffset::from(1_u128))],
                HornAtom::new(v3(), HornOffset::from(0_u128)),
            )
            .expect("a single-atom body is nonempty"),
            HornClause::new(
                &[
                    HornAtom::new(v1(), HornOffset::from(0_u128)),
                    HornAtom::new(v3(), HornOffset::from(2_u128)),
                ],
                HornAtom::new(v4(), HornOffset::from(0_u128)),
            )
            .expect("a two-atom body is nonempty"),
        ]
    }

    /// A total zero seed over the worked example's five variables.
    ///
    /// # Specification
    /// trivial.
    fn zero_seed() -> BTreeMap<HVar, ModelValue>
    {
        [v0(), v1(), v2(), v3(), v4()]
            .into_iter()
            .map(|variable| (variable, ModelValue::Finite(HornOffset::from(0_u128))))
            .collect()
    }

    /// Variable `a`, index 0.
    ///
    /// # Specification
    /// trivial.
    fn v0() -> HVar
    {
        HVar::Var(LevelVar::new(LevelVarIndex::from(0_u32)))
    }

    /// Variable `b`, index 1.
    ///
    /// # Specification
    /// trivial.
    fn v1() -> HVar
    {
        HVar::Var(LevelVar::new(LevelVarIndex::from(1_u32)))
    }

    /// Variable `c`, index 2.
    ///
    /// # Specification
    /// trivial.
    fn v2() -> HVar
    {
        HVar::Var(LevelVar::new(LevelVarIndex::from(2_u32)))
    }

    /// Variable `d`, index 3.
    ///
    /// # Specification
    /// trivial.
    fn v3() -> HVar
    {
        HVar::Var(LevelVar::new(LevelVarIndex::from(3_u32)))
    }

    /// Variable `e`, index 4.
    ///
    /// # Specification
    /// trivial.
    fn v4() -> HVar
    {
        HVar::Var(LevelVar::new(LevelVarIndex::from(4_u32)))
    }
}
