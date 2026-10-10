//! The typed profile: a scanner over caller-reported boundary events rather
//! than bytes.
//!
//! # The rule
//!
//! A caller walking a typed structure reports a boundary event wherever its
//! own grammar admits a cut — after a record, after a constructor closes —
//! carrying the tokens it consumed since the previous event and a residue
//! taken under the caller's committed hash rule. The scanner adds the tokens
//! to the pending count, then
//! cuts when the pending count has reached the hard token cap, or else when
//! the residue is divisible by kappa; a cut resets the pending count to zero.
//!
//! Kappa controls the expected number of events per content-defined cut under
//! a uniform residue distribution. The cap forces a cut at the first event
//! that reaches or exceeds it; a multi-token event can overshoot the cap.
//!
//! The scanner never sees bytes. A record-safe store whose records are its
//! boundary events, each one token, is the degenerate instance: kappa a power
//! of two plays the mask, the cap the record cap.
//!
//! # The committed fields
//!
//! ```text
//! profile fields := u64le kappa || u64le token cap
//! ```

use core::num::NonZeroU64;

use anodized::spec;

use crate::commitment::AlgorithmVersion;
use crate::commitment::CommitmentField;
use crate::commitment::CommitmentWriter;
use crate::commitment::ParameterCommitment;
use crate::error::ChunkerError;
use crate::error::InvalidParameterReason;
use crate::span::BoundaryReason;
use crate::units::BoundaryResidue;
use crate::units::TokenCount;

/// The expected number of boundary events per content-defined cut.
///
/// # Specification
/// - requires: nothing; the only constructor refuses zero.
/// - ensures: the carried value is non-zero.
/// - provides: a divisor the hash predicate can use without a zero check.
/// - fails: never, once constructed.
/// - panics: none.
/// - executable: none — the non-zero representation is enforced by the type;
///   validation predicates belong to the raw-value constructor.
///
/// # Adequacy
/// - hypothesis: L0 excludes a stored zero; L3 observes exact success values at
///   one, an ordinary value and the maximum, and the zero refusal reason. These
///   distinguish changed bounds, substituted values and wrong errors.
/// - witness: `tests::typed::zero_constants_are_refused_by_reason`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Kappa(NonZeroU64);

impl TryFrom<u64> for Kappa
{
    type Error = ChunkerError;

    /// Reads a kappa, refusing zero.
    ///
    /// # Specification
    /// - requires: nothing; the value is arbitrary.
    /// - ensures: on success the kappa carrying `raw`.
    /// - provides: the only way to obtain a kappa.
    /// - fails: [`ChunkerError::InvalidParameters`] with
    ///   [`InvalidParameterReason::ZeroKappa`] for zero.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ChunkerError::InvalidParameters`] — `raw` is zero.
    ///
    /// # Adequacy
    /// - hypothesis: L3 over arbitrary raw integers, with zero, one, seven and
    ///   the maximum as boundary witnesses; exact values and refusal reasons
    ///   distinguish broadened rejection, accepted zero and substituted values.
    /// - witness: `tests::typed::zero_constants_are_refused_by_reason`
    #[spec(ensures: |ret| match ret {
        Ok(value) => raw != 0 && value.0.get() == raw,
        Err(error) => raw == 0 && error == ChunkerError::InvalidParameters {
            reason: InvalidParameterReason::ZeroKappa,
        },
    })]
    #[inline]
    fn try_from(raw: u64) -> Result<Self, Self::Error>
    {
        NonZeroU64::new(raw)
            .map(Self)
            .ok_or(ChunkerError::InvalidParameters {
                reason: InvalidParameterReason::ZeroKappa,
            })
    }
}

impl From<NonZeroU64> for Kappa
{
    /// Takes a kappa that is non-zero by its type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(kappa: NonZeroU64) -> Self
    {
        Self(kappa)
    }
}

impl From<Kappa> for u64
{
    /// Reads the kappa back out.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(kappa: Kappa) -> Self
    {
        kappa.0.get()
    }
}

/// The most tokens a typed chunk may hold before the cap cuts it.
///
/// # Specification
/// - requires: nothing; the only constructor refuses zero.
/// - ensures: the carried value is non-zero.
/// - provides: a cap the scanner can reach.
/// - fails: never, once constructed.
/// - panics: none.
/// - executable: none — the non-zero representation is enforced by the type;
///   validation predicates belong to the raw-value constructor.
///
/// # Adequacy
/// - hypothesis: L0 excludes a stored zero; L3 observes exact success values at
///   one, an ordinary value and the maximum, and the zero refusal reason. These
///   distinguish changed bounds, substituted values and wrong errors.
/// - witness: `tests::typed::zero_constants_are_refused_by_reason`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TokenCap(NonZeroU64);

impl TryFrom<u64> for TokenCap
{
    type Error = ChunkerError;

    /// Reads a token cap, refusing zero.
    ///
    /// # Specification
    /// - requires: nothing; the value is arbitrary.
    /// - ensures: on success the cap carrying `raw`.
    /// - provides: the only way to obtain a cap.
    /// - fails: [`ChunkerError::InvalidParameters`] with
    ///   [`InvalidParameterReason::ZeroTokenCap`] for zero.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ChunkerError::InvalidParameters`] — `raw` is zero.
    ///
    /// # Adequacy
    /// - hypothesis: L3 over arbitrary raw integers, with zero, one, seven and
    ///   the maximum as boundary witnesses; exact values and refusal reasons
    ///   distinguish broadened rejection, accepted zero and substituted values.
    /// - witness: `tests::typed::zero_constants_are_refused_by_reason`
    #[spec(ensures: |ret| match ret {
        Ok(value) => raw != 0 && value.0.get() == raw,
        Err(error) => raw == 0 && error == ChunkerError::InvalidParameters {
            reason: InvalidParameterReason::ZeroTokenCap,
        },
    })]
    #[inline]
    fn try_from(raw: u64) -> Result<Self, Self::Error>
    {
        NonZeroU64::new(raw)
            .map(Self)
            .ok_or(ChunkerError::InvalidParameters {
                reason: InvalidParameterReason::ZeroTokenCap,
            })
    }
}

impl From<NonZeroU64> for TokenCap
{
    /// Takes a cap that is non-zero by its type.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(cap: NonZeroU64) -> Self
    {
        Self(cap)
    }
}

impl From<TokenCap> for u64
{
    /// Reads the cap back out.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(cap: TokenCap) -> Self
    {
        cap.0.get()
    }
}

impl From<TokenCap> for TokenCount
{
    /// Reads the cap as the token count it bounds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(cap: TokenCap) -> Self
    {
        Self::from(cap.0.get())
    }
}

/// The parameters of the typed profile.
///
/// # Specification
/// - requires: nothing beyond what [`Kappa`] and [`TokenCap`] enforce.
/// - ensures: two parameter sets are equal exactly when their commitments are
///   equal, because the commitment encodes both constants and nothing else.
/// - provides: the rule a typed scan cuts by, in a form a downstream root can
///   bind. The postcondition stays prose: it relates two parameter sets.
/// - fails: never, once constructed.
/// - panics: none.
/// - executable: none — injectivity relates two complete parameter sets; a
///   single construction has no second set to compare.
///
/// # Adequacy
/// - hypothesis: L2 agreement against a pinned golden written out field by
///   field, plus L3 for the claim that each constant moves the commitment.
/// - witness: `tests::commitment::the_typed_commitment_is_pinned`
/// - witness: `tests::commitment::each_typed_constant_moves_the_commitment`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct TypedChunkerParams
{
    /// The expected number of boundary events per content-defined cut.
    kappa: Kappa,
    /// The most tokens a chunk may hold.
    cap: TokenCap,
}

impl TypedChunkerParams
{
    /// Pairs a kappa with a cap.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        kappa: Kappa,
        cap: TokenCap,
    ) -> Self
    {
        Self { kappa, cap }
    }

    /// Returns kappa.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn kappa(&self) -> Kappa
    {
        self.kappa
    }

    /// Returns the token cap.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn cap(&self) -> TokenCap
    {
        self.cap
    }

    /// Returns the bytes a downstream root commits this profile as.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`crate::PARAMETER_DOMAIN`], the
    ///   [`AlgorithmVersion::TypedCdc`] discriminator, kappa, then the cap,
    ///   every integer little-endian at its fixed width.
    /// - provides: the opaque bytes a root binds, so two writers that disagree
    ///   on either constant produce different roots rather than silently
    ///   different cuts.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 observes a field-by-field golden for positive kappa and
    ///   cap; L3 changes each independently and swaps them. Wrong framing,
    ///   width, endian order, omission and field swaps change the byte image.
    /// - witness: `tests::commitment::the_typed_commitment_is_pinned`
    /// - witness: `tests::commitment::each_typed_constant_moves_the_commitment`
    #[spec(ensures: |ret| {
        let bytes = ret.as_ref();
        let domain = crate::commitment::PARAMETER_DOMAIN;
        bytes.starts_with(domain)
            && bytes.len() == domain.len().saturating_add(18)
            && bytes.get(domain.len()..domain.len().saturating_add(2)) == Some([2, 0].as_slice())
            && bytes.get(domain.len().saturating_add(2)..domain.len().saturating_add(10))
                == Some(u64::from(self.kappa).to_le_bytes().as_slice())
            && bytes.get(domain.len().saturating_add(10)..)
                == Some(u64::from(self.cap).to_le_bytes().as_slice())
    })]
    #[inline]
    #[must_use]
    pub fn commitment(&self) -> ParameterCommitment
    {
        let mut writer = CommitmentWriter::open(AlgorithmVersion::TypedCdc);
        writer.push(CommitmentField::Long(u64::from(self.kappa)));
        writer.push(CommitmentField::Long(u64::from(self.cap)));

        writer.finish()
    }
}

/// One place the caller's grammar admits a cut.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct BoundaryEvent
{
    /// The tokens consumed since the previous event.
    tokens: TokenCount,
    /// The rolling hash of the subtree the event closes.
    residue: BoundaryResidue,
}

impl BoundaryEvent
{
    /// Reports an event: the tokens since the previous one, and the residue of
    /// the subtree this one closes.
    ///
    /// # Specification
    /// - requires: `tokens` counts only what was consumed since the previous
    ///   event, never a subtree's whole size; the scanner adds every event's
    ///   count to the pending total, so a cumulative count would be counted
    ///   again at each enclosing event.
    /// - ensures: the event carries both values unchanged.
    /// - provides: the scanner's one input.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on ordered incremental events below, at and above the
    ///   cap, with residues beside and on a multiple; decisions and pending
    ///   counts distinguish swapped fields and cumulative double counting.
    /// - witness: `tests::typed::the_cap_and_the_predicate_cut_at_their_boundaries`
    /// - witness: `tests::typed::zero_token_events_still_observe_the_residue`
    #[spec(ensures: |ret| matches!(ret.tokens.const_eq(tokens), crate::units::ConstEquality::Equal) && matches!(ret.residue.const_eq(residue), crate::units::ConstEquality::Equal))]
    #[inline]
    #[must_use]
    pub const fn new(
        tokens: TokenCount,
        residue: BoundaryResidue,
    ) -> Self
    {
        Self { tokens, residue }
    }

    /// Returns the tokens consumed since the previous event.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn tokens(&self) -> TokenCount
    {
        self.tokens
    }

    /// Returns the residue of the subtree the event closes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn residue(&self) -> BoundaryResidue
    {
        self.residue
    }
}

/// What the scanner decided at one boundary event.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CutDecision
{
    /// The chunk ends at this event, for this reason.
    Cut(BoundaryReason),
    /// The chunk continues past this event.
    Continue,
}

/// The typed scanner: the pending token count of the open chunk, and the rule
/// that cuts it.
///
/// # Specification
/// - requires: events arrive in the caller's canonical order.
/// - ensures: every decision is a function of the parameters, the pending
///   count, and the event alone — no clock, no randomness, no lookahead.
/// - provides: content-defined cuts at the caller's own boundaries, so a cut a
///   subtree induces travels with that subtree.
/// - fails: never.
/// - panics: none.
/// - executable: none — absence of clocks, randomness and lookahead is a
///   whole-execution property, not a predicate on one stored scanner.
///
/// # Adequacy
/// - hypothesis: L3 on canonical event sequences at both cut boundaries; exact
///   decisions and pending counts distinguish cap precedence changes, premature
///   cuts and failure to reset. Finite executions witness these sequences, not
///   universal determinism.
/// - witness: `tests::typed::the_cap_and_the_predicate_cut_at_their_boundaries`
/// - witness: `tests::typed::the_cap_takes_precedence_over_the_predicate`
/// - witness: `tests::typed::a_saturated_count_still_cuts`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct TypedChunker
{
    /// The rule.
    params: TypedChunkerParams,
    /// The tokens in the open chunk.
    pending: TokenCount,
}

impl TypedChunker
{
    /// Opens a scan with an empty chunk.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(params: &TypedChunkerParams) -> Self
    {
        Self {
            params: *params,
            pending: TokenCount::ZERO,
        }
    }

    /// Returns the rule the scan cuts by.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn params(&self) -> TypedChunkerParams
    {
        self.params
    }

    /// Returns the tokens in the open chunk.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn pending(&self) -> TokenCount
    {
        self.pending
    }

    /// Applies the rule at one boundary event.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the event's tokens join the pending count, saturating at the
    ///   width; then [`CutDecision::Cut`] with [`BoundaryReason::MaxTokenCap`]
    ///   when the pending count has reached the cap, else with
    ///   [`BoundaryReason::HashPredicate`] when the residue is divisible by
    ///   kappa, else [`CutDecision::Continue`]. A cut leaves the pending count
    ///   zero; a continuation leaves the sum.
    /// - provides: the scanner's one step. Saturation is the safe direction: a
    ///   saturated count reaches every cap and cuts.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 only — the decision surface is the cap comparison and
    ///   the divisibility test; each is separated by its boundary pair (one
    ///   token under the cap against exactly the cap, a residue one off a
    ///   multiple of kappa against the multiple), with the precedence of the
    ///   cap over the predicate and the reset after each cut asserted.
    ///   Zero-token events exercise the empty increment; overflow exercises
    ///   saturation rather than wrapping below the cap.
    /// - witness: `tests::typed::the_cap_and_the_predicate_cut_at_their_boundaries`
    /// - witness: `tests::typed::the_cap_takes_precedence_over_the_predicate`
    /// - witness: `tests::typed::one_event_per_record_is_the_record_safe_degenerate_instance`
    /// - witness: `tests::typed::a_saturated_count_still_cuts`
    /// - witness: `tests::typed::zero_token_events_still_observe_the_residue`
    #[spec(
        captures: pending = self.pending.saturating_plus(event.tokens),
        ensures: |ret| match ret {
            CutDecision::Cut(BoundaryReason::MaxTokenCap) =>
                pending >= TokenCount::from(self.params.cap) && self.pending == TokenCount::ZERO,
            CutDecision::Cut(BoundaryReason::HashPredicate) =>
                pending < TokenCount::from(self.params.cap)
                    && u64::from(event.residue).is_multiple_of(u64::from(self.params.kappa))
                    && self.pending == TokenCount::ZERO,
            CutDecision::Continue => pending < TokenCount::from(self.params.cap)
                && !u64::from(event.residue).is_multiple_of(u64::from(self.params.kappa))
                && self.pending == pending,
            CutDecision::Cut(_) => false,
        },
    )]
    #[inline]
    #[must_use]
    pub fn on_boundary(
        &mut self,
        event: BoundaryEvent,
    ) -> CutDecision
    {
        let pending = self.pending.saturating_plus(event.tokens);
        let residue = u64::from(event.residue);
        let divisible = residue.checked_rem(u64::from(self.params.kappa)) == Some(0_u64);

        let decision = if pending >= TokenCount::from(self.params.cap) {
            CutDecision::Cut(BoundaryReason::MaxTokenCap)
        }
        else if divisible {
            CutDecision::Cut(BoundaryReason::HashPredicate)
        }
        else {
            CutDecision::Continue
        };

        self.pending = match decision {
            | CutDecision::Cut(_) => TokenCount::ZERO,
            | CutDecision::Continue => pending,
        };

        decision
    }
}
