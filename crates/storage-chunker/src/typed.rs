//! The typed profile: a scanner over caller-reported boundary events rather
//! than bytes.
//!
//! # The rule
//!
//! A caller walking a typed structure reports a boundary event wherever its
//! own grammar admits a cut — after a record, after a constructor closes —
//! carrying the tokens it consumed since the previous event and a residue,
//! a rolling hash of the subtree the event closes, taken under the caller's
//! own committed hash. The scanner adds the tokens to the pending count, then
//! cuts when the pending count has reached the hard token cap, or else when
//! the residue is divisible by kappa; a cut resets the pending count to zero.
//!
//! Kappa is the expected number of boundary events per content-defined cut: a
//! residue uniform over its width is divisible by kappa with probability one
//! over kappa. The cap bounds every chunk's tokens whatever the residues do.
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
    /// - witness: `tests::typed::the_cap_and_the_predicate_cut_at_their_boundaries`
    /// - witness: `tests::typed::the_cap_takes_precedence_over_the_predicate`
    /// - witness: `tests::typed::one_event_per_record_is_the_record_safe_degenerate_instance`
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
