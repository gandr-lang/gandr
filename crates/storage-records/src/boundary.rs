//! Where leaves end: the content-defined boundary rule, its committed
//! parameters, and the spans it cuts a sorted record sequence into.
//!
//! # Why the cut is content-defined
//!
//! A tree whose leaves end at fixed positions loses sharing under any edit that
//! shifts positions: insert one record near the front and every later leaf is
//! renumbered, so no leaf downstream of the edit is reusable. A tree whose
//! leaves end where the *data* says keeps sharing, because the cut a record
//! induces travels with that record.
//!
//! # The rule
//!
//! A record ends a leaf when the digest of its canonical encoding, taken under
//! the boundary domain, has [`BoundaryMaskBits`] low zero bits — a decision
//! that reads one record and nothing else. A cap ([`BoundaryRecordCap`]) ends a
//! leaf that the digest rule has not ended, which bounds leaf size at the cost
//! of making the cut position-dependent inside one capped run: an edit can move
//! a capped cut, but only within the run it falls in, never past the next
//! digest-induced cut.
//!
//! The parameters are protocol constants, not tuning knobs: two writers that
//! disagree on them build different trees from the same records. They are
//! therefore committed — [`BoundaryParams::commitment`] goes into the hashed
//! root manifest, so a root states the rule its leaves were cut by.

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::fmt;

use anodized::spec;

use crate::bytes::OwnedRecordEncoding;
use crate::bytes::RecordEncoding;
use crate::error::RecordTreeError;
use crate::record::RecordIndex;
use crate::record::RecordRef;
use crate::wire::Domain;
use crate::wire::WireBuffer;
use crate::wire::WireBytes;
use crate::wire::WireLong;
use crate::wire::WireTag;
use crate::wire::digest;

/// The number of low zero bits a record digest needs to end a leaf.
///
/// The expected number of records per leaf is two to this power, so the value
/// selects the mean leaf size directly.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BoundaryMaskBits(u8);

impl BoundaryMaskBits
{
    /// The largest admissible width.
    /// The expected number of records per leaf is two to this power, so the
    /// ceiling bounds the mean leaf size at two to the 32nd power records, far
    /// past any tree this crate serves.
    pub const MAX: Self = Self(32_u8);

    /// The smallest admissible width.
    ///
    /// Zero would make every record a boundary, collapsing every leaf to one
    /// record and the tree to a list of singleton leaves.
    pub const MIN: Self = Self(1_u8);

    /// Reports whether a digest prefix satisfies this width.
    ///
    /// The width is always at most [`BoundaryMaskBits::MAX`], which the
    /// prefix's 64-bit window holds, so the mask is exact.
    ///
    /// # Specification
    /// - requires: `(Self::MIN.0 ..= Self::MAX.0).contains(&self.0)` — `self`
    ///   is built through the only constructor, so the width is admissible and
    ///   the mask exact.
    /// - ensures: `|ret| (ret == BoundaryDecision::EndsLeaf) ==
    ///   (u64::from(prefix).trailing_zeros() >= u32::from(self.0))` — reports
    ///   `EndsLeaf` exactly when the prefix's masked bits are all zero.
    /// - provides: the digest side of the boundary rule, against which a
    ///   committed commitment is checked.
    /// - fails: none — the decision is total.
    /// - panics: none.
    #[inline]
    #[must_use]
    #[spec(
        requires: (Self::MIN.0 ..= Self::MAX.0).contains(&self.0),
        ensures: |ret| (ret == BoundaryDecision::EndsLeaf)
            == (u64::from(prefix).trailing_zeros() >= u32::from(self.0)),
    )]
    fn ends_leaf(
        self,
        prefix: DigestPrefix,
    ) -> BoundaryDecision
    {
        let mask = (1_u64 << u32::from(self.0)).saturating_sub(1_u64);

        if u64::from(prefix) & mask == 0_u64 {
            BoundaryDecision::EndsLeaf
        }
        else {
            BoundaryDecision::Continues
        }
    }
}

/// The leading bits of a boundary digest, read as one number.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DigestPrefix(u64);

impl From<u64> for DigestPrefix
{
    /// Reads a `u64` as a digest prefix.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(prefix: u64) -> Self
    {
        Self(prefix)
    }
}

impl From<DigestPrefix> for u64
{
    /// Reads the prefix back out as a `u64`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(prefix: DigestPrefix) -> Self
    {
        prefix.0
    }
}

impl TryFrom<u8> for BoundaryMaskBits
{
    type Error = RecordTreeError;

    /// Builds a mask width after rejecting one outside the admissible range.
    ///
    /// # Specification
    /// - requires: nothing; the width is caller-supplied and arbitrary.
    /// - ensures: on success the width lies in [`BoundaryMaskBits::MIN`] to
    ///   [`BoundaryMaskBits::MAX`] inclusive, so the mask it induces is a
    ///   non-empty subset of the bits the predicate reads.
    /// - provides: the only constructor, so no downstream code re-checks the
    ///   range.
    /// - fails: [`RecordTreeError::IncompatibleParameters`] outside the range.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::IncompatibleParameters`] — the width is zero or
    /// wider than the predicate reads.
    ///
    /// # Adequacy
    /// - hypothesis: L3 only — the decision surface is the two range
    ///   comparisons, separated exhaustively by the four boundary values around
    ///   the admissible interval.
    /// - witness: `boundary::tests::mask_bits_admit_the_interval_and_refuse_outside`
    #[inline]
    #[spec(ensures: |ret| ret.is_ok() == (Self::MIN.0..=Self::MAX.0).contains(&bits))]
    fn try_from(bits: u8) -> Result<Self, Self::Error>
    {
        if !(Self::MIN.0 ..= Self::MAX.0).contains(&bits) {
            return Err(RecordTreeError::IncompatibleParameters {
                context: "boundary mask width is outside the admissible range".into(),
            });
        }

        Ok(Self(bits))
    }
}

impl From<BoundaryMaskBits> for u8
{
    /// Reads the mask width back out as a `u8`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bits: BoundaryMaskBits) -> Self
    {
        bits.0
    }
}

impl fmt::Display for BoundaryMaskBits
{
    /// Writes the mask width.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the carried width through the `u8` rendering, so the
    ///   width and fill options the caller set apply to it.
    /// - provides: the width a parameter refusal names.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        self.0.fmt(f)
    }
}

/// The largest number of records one leaf may hold before the cap ends it.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BoundaryRecordCap(u32);

impl BoundaryRecordCap
{
    /// Returns the cap as a run length.
    ///
    /// Every target this crate builds for has a pointer at least as wide as
    /// thirty-two bits, so the widening is exact; a narrower target saturates,
    /// which can only end a run earlier and never later.
    ///
    /// # Specification
    /// - requires: nothing; the cap is committed at seal time.
    /// - ensures: `|ret| usize::from(ret) ==
    ///   usize::try_from(self.0).unwrap_or(usize::MAX)` — the exact run length
    ///   on every target this crate builds for, and the host ceiling on a
    ///   narrower one.
    /// - provides: the host-width widening a span walk consumes.
    /// - fails: none — saturation can only end a run earlier.
    /// - panics: none.
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| usize::from(ret) == usize::try_from(self.0).unwrap_or(usize::MAX))]
    fn as_run_length(self) -> LeafRunLength
    {
        LeafRunLength(usize::try_from(self.0).unwrap_or(usize::MAX))
    }
}

impl TryFrom<u32> for BoundaryRecordCap
{
    type Error = RecordTreeError;

    /// Builds a cap after rejecting a cap of zero.
    ///
    /// # Specification
    /// - requires: nothing; the cap is caller-supplied and arbitrary.
    /// - ensures: on success the cap is at least one, so every span the rule
    ///   emits is non-empty and the span walk always advances.
    /// - provides: the only constructor, so the span walk needs no guard
    ///   against a zero-length span.
    /// - fails: [`RecordTreeError::IncompatibleParameters`] on zero.
    /// - panics: none.
    ///
    /// # Errors
    /// [`RecordTreeError::IncompatibleParameters`] — the cap is zero.
    ///
    /// # Adequacy
    /// - hypothesis: L3 only — the decision surface is the comparison against
    ///   zero, separated by zero (refused) and one (admitted).
    /// - witness: `boundary::tests::record_cap_refuses_zero`
    #[inline]
    #[spec(ensures: |ret| ret.is_ok() == (cap != 0_u32))]
    fn try_from(cap: u32) -> Result<Self, Self::Error>
    {
        if cap == 0_u32 {
            return Err(RecordTreeError::IncompatibleParameters {
                context: "boundary record cap is zero".into(),
            });
        }

        Ok(Self(cap))
    }
}

/// How many records a leaf run holds so far.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LeafRunLength(usize);

impl From<usize> for LeafRunLength
{
    /// Reads a `usize` as a run length.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(length: usize) -> Self
    {
        Self(length)
    }
}

impl From<LeafRunLength> for usize
{
    /// Reads the run length back out as a `usize`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(length: LeafRunLength) -> Self
    {
        length.0
    }
}

impl From<BoundaryRecordCap> for u32
{
    /// Reads the cap back out as a `u32`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(cap: BoundaryRecordCap) -> Self
    {
        cap.0
    }
}

impl fmt::Display for BoundaryRecordCap
{
    /// Writes the cap.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the carried cap through the `u32` rendering, so the
    ///   width and fill options the caller set apply to it.
    /// - provides: the cap a parameter refusal names.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        self.0.fmt(f)
    }
}

/// Which boundary rule a tree's leaves were cut by.
///
/// One variant is not an accident of being early: the rule is protocol
/// material, and a second rule enters by being named here and committed in the
/// same bytes, never by a parameter a reader has to guess.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum BoundaryProfile
{
    /// A leaf ends at a record whose own digest satisfies the mask.
    RecordDigest,
}

impl BoundaryProfile
{
    /// The profile newly built trees are cut by.
    pub const CURRENT: Self = Self::RecordDigest;

    /// Returns the discriminator this profile is committed under.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one fixed byte per profile, distinct across the enum, and
    ///   never derived from the variant's position.
    /// - provides: the discriminator a boundary commitment opens with, so
    ///   reordering this enum cannot change a committed root.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    const fn tag(self) -> WireTag
    {
        match self {
            | Self::RecordDigest => WireTag(0x01_u8),
        }
    }
}

/// The committed parameters of a boundary rule.
///
/// # Specification
/// - requires: nothing beyond what the component constructors enforce.
/// - ensures: two parameter sets are equal exactly when their commitments are
///   equal, because the commitment encodes every field and nothing else.
/// - provides: the rule a tree's leaves were cut by, in a form a root manifest
///   can hash. The postcondition stays prose: it relates two parameter sets,
///   and a data specification's `maintains` is not evaluated when a value is
///   constructed, so a clause here would be inert.
/// - fails: never, once constructed.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 agreement — the commitment is exercised as a pinned golden
///   against the default profile's exact bytes, and L3 pointwise for the claim
///   that a changed field changes the commitment, one boundary pair per field.
/// - witness: `boundary::tests::default_commitment_is_pinned`
/// - witness: `boundary::tests::each_field_moves_the_commitment`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct BoundaryParams
{
    /// The rule in force.
    profile: BoundaryProfile,
    /// The digest mask width.
    mask_bits: BoundaryMaskBits,
    /// The per-leaf record cap.
    record_cap: BoundaryRecordCap,
}

impl BoundaryParams
{
    /// Builds a parameter set from explicit choices.
    ///
    /// # Specification
    /// - requires: `mask_bits` and `record_cap` were minted through their own
    ///   fallible conversions, which is the only way to obtain either.
    /// - ensures: the set carries exactly the three choices offered.
    /// - provides: the only way to state a boundary rule, so a rule is always
    ///   three deliberate choices.
    /// - fails: never — the range checks live in the two conversions.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub const fn new(
        profile: BoundaryProfile,
        mask_bits: BoundaryMaskBits,
        record_cap: BoundaryRecordCap,
    ) -> Self
    {
        Self {
            profile,
            mask_bits,
            record_cap,
        }
    }

    /// Builds the parameter set newly built trees use.
    ///
    /// The mask width gives leaves of sixteen records on average and the cap
    /// gives a hard ceiling four times that, so a capped run stays a small
    /// multiple of the mean rather than an unrelated size.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the current profile, a mask width of four, and a cap of
    ///   sixty-four — the mean and ceiling the paragraph above relates.
    /// - provides: the rule newly built trees are cut by, named in one place so
    ///   a writer and a reader cannot disagree on it.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub const fn current() -> Self
    {
        Self::new(
            BoundaryProfile::CURRENT,
            BoundaryMaskBits(4_u8),
            BoundaryRecordCap(64_u32),
        )
    }

    /// Returns the rule in force.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn profile(&self) -> BoundaryProfile
    {
        self.profile
    }

    /// Returns the digest mask width.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn mask_bits(&self) -> BoundaryMaskBits
    {
        self.mask_bits
    }

    /// Returns the per-leaf record cap.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn record_cap(&self) -> BoundaryRecordCap
    {
        self.record_cap
    }

    /// Returns the bytes a root manifest commits these parameters as.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the profile tag, then the mask width, then the cap as a
    ///   wire-width number, in that order; the bytes are a function of the
    ///   three parameters alone.
    /// - provides: the opaque bytes a root binds instead of the parsed
    ///   parameters, so a reader that does not implement a profile refuses a
    ///   root built under it rather than misreading one.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub fn commitment(&self) -> ProfileCommitment
    {
        let mut bytes = WireBuffer::new();
        bytes.push_tag(self.profile.tag());
        bytes.push_tag(WireTag::from(u8::from(self.mask_bits)));
        bytes.push_long(WireLong::from(u64::from(u32::from(self.record_cap))));

        ProfileCommitment::from(Vec::<u8>::from(bytes))
    }

    /// Reports whether `record` ends the leaf it falls in.
    ///
    /// # Specification
    /// - requires: `record` is the encoding of a leaf-start record.
    /// - ensures: reports `EndsLeaf` exactly when the record's digest has every
    ///   masked bit clear.
    /// - provides: the digest side of the run rule; the record-cap side is
    ///   applied by the span walk. The postcondition stays prose: the decision
    ///   is [`BoundaryMaskBits::ends_leaf`]'s, which carries it as a clause,
    ///   and restating the digest here would be this body again.
    /// - fails: none — the decision is total.
    /// - panics: none.
    #[inline]
    #[must_use]
    fn cuts_after(
        self,
        record: RecordEncoding<'_>,
    ) -> BoundaryDecision
    {
        match self.profile {
            | BoundaryProfile::RecordDigest => {
                let hash = digest(Domain::Boundary, WireBytes::from(record.as_ref()));
                let mut leading = [0_u8; 8_usize];
                let (head, _tail) = hash.as_ref().split_at(leading.len());
                leading.copy_from_slice(head);

                self.mask_bits
                    .ends_leaf(DigestPrefix::from(u64::from_le_bytes(leading)))
            },
        }
    }
}

impl Default for BoundaryParams
{
    /// Builds the parameter set newly built trees use.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: exactly what [`BoundaryParams::current`] returns, so the
    ///   default and the build's own rule cannot drift apart.
    /// - provides: the default a caller reaches without naming three fields.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    fn default() -> Self
    {
        Self::current()
    }
}

/// The committed bytes of a boundary rule, opaque to everything that carries
/// them.
///
/// A root binds these bytes rather than the parsed parameters, so a reader that
/// does not implement a profile still refuses a root built under it instead of
/// misreading one.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ProfileCommitment(Box<[u8]>);

impl From<Vec<u8>> for ProfileCommitment
{
    /// Takes over a byte vector as committed boundary bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: Vec<u8>) -> Self
    {
        Self(bytes.into_boxed_slice())
    }
}

impl From<Box<[u8]>> for ProfileCommitment
{
    /// Takes over an owned boxed slice as committed boundary bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: Box<[u8]>) -> Self
    {
        Self(bytes)
    }
}

impl AsRef<[u8]> for ProfileCommitment
{
    /// Borrows the committed bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        self.0.as_ref()
    }
}

/// Whether a record ends the leaf it falls in.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BoundaryDecision
{
    /// The leaf ends after this record.
    EndsLeaf,
    /// The leaf continues past this record.
    Continues,
}

/// A half-open run of record positions forming one leaf.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct RecordSpan
{
    /// The first position in the run.
    start: RecordIndex,
    /// One past the last position in the run.
    end: RecordIndex,
}

impl RecordSpan
{
    /// Returns the run that holds no positions.
    ///
    /// The rule never emits this span; a tree with no records still has one
    /// leaf, and that leaf's run is this one.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a run whose start and end are both the first position, so it
    ///   holds no position.
    /// - provides: the run of the single leaf a record-less tree still has, for
    ///   the reason the paragraph above states.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub const fn empty() -> Self
    {
        Self {
            start: RecordIndex::ZERO,
            end: RecordIndex::ZERO,
        }
    }

    /// Returns the first position in the run.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn start(&self) -> RecordIndex
    {
        self.start
    }

    /// Returns one past the last position in the run.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn end(&self) -> RecordIndex
    {
        self.end
    }
}

/// The canonical encoding of one record, as the boundary rule reads it.
///
/// The encoding is length-prefixed on both fields and domain-tagged, so a key
/// and a value cannot be re-split at a different position to make the same
/// bytes — which would make one record's boundary decision depend on a
/// different record's content.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the encoding is injective in the key-value pair: distinct pairs
///   give distinct bytes, because both lengths precede both bodies.
/// - provides: the boundary rule's input, and the only place a record becomes
///   bytes outside a node encoding. The postcondition stays prose: injectivity
///   relates two key-value pairs, and one call encodes one pair.
/// - fails: [`RecordTreeError::ArithmeticOverflow`] when a key or value length
///   exceeds the wire width.
/// - panics: none.
///
/// # Errors
/// [`RecordTreeError::ArithmeticOverflow`] — a field length exceeds `u64`.
///
/// # Adequacy
/// - hypothesis: L3 only — the injectivity claim's decision surface is the
///   field framing, killed by the length-prefix ambiguity trap pair (`("ab",
///   "c")` against `("a", "bc")`) asserted to give different bytes.
/// - witness: `boundary::tests::record_encoding_separates_the_ambiguity_pair`
pub(crate) fn encode_record(record: RecordRef<'_>) -> Result<OwnedRecordEncoding, RecordTreeError>
{
    let mut bytes = WireBuffer::new();
    bytes.push_domain(Domain::Record);
    bytes.push_length_prefixed(
        WireBytes::from(record.key().as_ref()),
        "record key length".into(),
    )?;
    bytes.push_length_prefixed(
        WireBytes::from(record.value().as_ref()),
        "record value length".into(),
    )?;

    Ok(OwnedRecordEncoding::from(Vec::<u8>::from(bytes)))
}

/// Cuts a sorted record sequence into the leaves the rule induces.
///
/// # Specification
/// - requires: `records` is the tree's whole record sequence in key order.
/// - ensures: `|ret| ret.as_ref().ok().is_none_or(|spans|
///   spans.iter().all(|span| span.start() < span.end()) &&
///   spans.first().is_none_or(|span| span.start() == RecordIndex::ZERO) &&
///   spans.iter().zip(spans.iter().skip(1)).all(|(earlier, later)|
///   earlier.end() == later.start()) && spans.last().map_or(records.is_empty(),
///   |span| usize::from(span.end()) == records.len()))` — the returned spans
///   partition the positions of `records` in increasing order with no gap and
///   no overlap, every span is non-empty, and an empty input gives no spans.
///   Which positions the cuts fall at is the rule's own: a run ended by the cap
///   depends additionally on where the previous cut fell.
/// - provides: the leaf boundaries the builder encodes.
/// - fails: [`RecordTreeError::ArithmeticOverflow`] when a record cannot be
///   encoded for the rule, or when a position exceeds the host width.
/// - panics: none.
/// - intension: exactly one pass over `records`, one record encoding and one
///   digest per record, and no lookahead — the promised property is that a
///   record's own decision never reads a later record, which is what makes the
///   partition local. The observation is the returned partition itself.
///
/// # Errors
/// [`RecordTreeError::ArithmeticOverflow`] — a record's fields or a position
/// exceed their widths.
///
/// # Adequacy
/// - hypothesis: L2 agreement for the partition law — a property over generated
///   corpora asserts the spans reassemble the input exactly — plus L3 for the
///   two cut causes, separated by a corpus with a digest-induced cut and by a
///   corpus of cap-length runs, and by the empty input.
/// - witness: `boundary::tests::spans_partition_the_input`
/// - witness: `boundary::tests::the_cap_ends_a_run_the_digest_does_not`
/// - witness: `boundary::tests::an_empty_input_has_no_spans`
#[spec(ensures: |ret| ret.as_ref().ok().is_none_or(|spans| {
    spans.iter().all(|span| span.start() < span.end())
        && spans.first().is_none_or(|span| span.start() == RecordIndex::ZERO)
        && spans
            .iter()
            .zip(spans.iter().skip(1_usize))
            .all(|(earlier, later)| earlier.end() == later.start())
        && spans
            .last()
            .map_or(records.is_empty(), |span| usize::from(span.end()) == records.len())
}))]
pub(crate) fn leaf_spans(
    records: &[RecordRef<'_>],
    params: BoundaryParams,
) -> Result<Box<[RecordSpan]>, RecordTreeError>
{
    let mut spans = Vec::<RecordSpan>::new();
    let mut start = RecordIndex::ZERO;
    let mut position = RecordIndex::ZERO;
    let cap = params.record_cap().as_run_length();

    for record in records {
        let encoded = encode_record(*record)?;
        position = position.next()?;

        let run_length = usize::from(position)
            .checked_sub(usize::from(start))
            .map(LeafRunLength::from)
            .ok_or_else(|| RecordTreeError::ArithmeticOverflow {
                context: "leaf run length".into(),
            })?;
        let ends = params.cuts_after(encoded.as_borrowed()) == BoundaryDecision::EndsLeaf
            || run_length >= cap;

        if ends {
            spans.push(RecordSpan {
                start,
                end: position,
            });
            start = position;
        }
    }

    if start != position {
        spans.push(RecordSpan {
            start,
            end: position,
        });
    }

    Ok(spans.into_boxed_slice())
}

#[cfg(test)]
mod tests
{
    use alloc::vec;
    use alloc::vec::Vec;

    use super::BoundaryMaskBits;
    use super::BoundaryParams;
    use super::BoundaryProfile;
    use super::BoundaryRecordCap;
    use super::encode_record;
    use super::leaf_spans;
    use crate::error::RecordTreeError;
    use crate::record::Record;
    use crate::record::RecordCount;
    use crate::record::RecordRef;

    /// A corpus of `count` records with distinct keys in key order.
    ///
    /// # Specification
    /// - requires: nothing; a count of zero yields no record.
    /// - ensures: exactly `count` records whose keys are the zero-padded
    ///   decimal positions, so they are distinct and already in key order.
    /// - provides: the corpus every span fixture below is cut from, ordered so
    ///   a test never depends on the build's own sorting.
    /// - panics: none.
    fn corpus(count: RecordCount) -> Vec<Record>
    {
        let mut records = Vec::new();

        for index in 0_u64 .. u64::from(count) {
            records.push(Record::new(
                alloc::format!("key-{index:08}").into_bytes(),
                alloc::format!("value-{index:08}").into_bytes(),
            ));
        }

        records
    }

    /// Borrows a corpus as the record references the rule takes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: exactly one borrowed reference per element of `records`, in
    ///   the order `records` holds them, so nothing is dropped, added, or
    ///   permuted.
    /// - provides: the reference sequence the rule takes, matching the corpus
    ///   position for position.
    /// - fails: never.
    /// - panics: none.
    fn borrow(records: &[Record]) -> Vec<RecordRef<'_>>
    {
        records.iter().map(Record::as_record_ref).collect()
    }

    #[test]
    fn mask_bits_admit_the_interval_and_refuse_outside()
    {
        assert!(BoundaryMaskBits::try_from(0_u8).is_err());
        assert_eq!(BoundaryMaskBits::try_from(1_u8), Ok(BoundaryMaskBits::MIN));
        assert_eq!(BoundaryMaskBits::try_from(32_u8), Ok(BoundaryMaskBits::MAX));
        assert_eq!(
            BoundaryMaskBits::try_from(33_u8),
            Err(RecordTreeError::IncompatibleParameters {
                context: "boundary mask width is outside the admissible range".into(),
            })
        );
    }

    #[test]
    fn record_cap_refuses_zero()
    {
        assert_eq!(
            BoundaryRecordCap::try_from(0_u32),
            Err(RecordTreeError::IncompatibleParameters {
                context: "boundary record cap is zero".into(),
            })
        );
        assert!(BoundaryRecordCap::try_from(1_u32).is_ok());
    }

    #[test]
    fn default_commitment_is_pinned()
    {
        let commitment = BoundaryParams::current().commitment();

        // Hand check of the record-cap field: the current cap is 64, which is
        // 0x40, and a little-endian long writes the low byte first, so the
        // commitment is the profile tag, the mask-width tag, 0x40 and seven
        // zero bytes.
        assert_eq!(
            commitment.as_ref(),
            [
                0x01_u8, 0x04_u8, 0x40_u8, 0x00_u8, 0x00_u8, 0x00_u8, 0x00_u8, 0x00_u8, 0x00_u8,
                0x00_u8,
            ]
            .as_slice()
        );
    }

    #[test]
    fn each_field_moves_the_commitment()
    {
        let base = BoundaryParams::current();
        let wider = BoundaryParams::new(
            BoundaryProfile::CURRENT,
            BoundaryMaskBits::try_from(5_u8).expect("five is admissible"),
            base.record_cap(),
        );
        let capped = BoundaryParams::new(
            BoundaryProfile::CURRENT,
            base.mask_bits(),
            BoundaryRecordCap::try_from(65_u32).expect("sixty-five is admissible"),
        );

        assert_ne!(base.commitment(), wider.commitment());
        assert_ne!(base.commitment(), capped.commitment());
    }

    #[test]
    fn record_encoding_separates_the_ambiguity_pair()
    {
        let left = encode_record(RecordRef::new(b"ab", b"c")).expect("lengths fit");
        let right = encode_record(RecordRef::new(b"a", b"bc")).expect("lengths fit");

        assert_ne!(left, right);
    }

    #[test]
    fn spans_partition_the_input()
    {
        let owned = corpus(RecordCount::from(500_u64));
        let records = borrow(owned.as_slice());
        let spans =
            leaf_spans(records.as_slice(), BoundaryParams::current()).expect("the corpus encodes");

        let mut expected_start = 0_usize;
        for span in spans.as_ref() {
            assert_eq!(usize::from(span.start()), expected_start);
            assert!(usize::from(span.end()) > usize::from(span.start()));
            expected_start = usize::from(span.end());
        }
        assert_eq!(expected_start, records.len());
        assert!(spans.len() > 1_usize, "the corpus produces several leaves");
    }

    #[test]
    fn the_cap_ends_a_run_the_digest_does_not()
    {
        let owned = corpus(RecordCount::from(64_u64));
        let records = borrow(owned.as_slice());
        // A mask this wide makes a digest-induced cut vanishingly unlikely over
        // a corpus this small, so every cut observed is the cap's.
        let params = BoundaryParams::new(
            BoundaryProfile::CURRENT,
            BoundaryMaskBits::MAX,
            BoundaryRecordCap::try_from(8_u32).expect("eight is admissible"),
        );
        let spans = leaf_spans(records.as_slice(), params).expect("the corpus encodes");

        assert_eq!(spans.len(), 8_usize);
        for span in spans.as_ref() {
            let length = usize::from(span.end()).saturating_sub(usize::from(span.start()));
            assert_eq!(length, 8_usize);
        }
    }

    #[test]
    fn an_empty_input_has_no_spans()
    {
        let spans = leaf_spans(&[], BoundaryParams::current()).expect("nothing to encode");

        assert_eq!(spans.as_ref(), [].as_slice());
    }

    #[test]
    fn a_records_decision_reads_only_that_record()
    {
        let owned = corpus(RecordCount::from(200_u64));
        let records = borrow(owned.as_slice());
        let params = BoundaryParams::current();
        let full = leaf_spans(records.as_slice(), params).expect("the corpus encodes");

        // Re-cutting the suffix that starts at the first cut reproduces the
        // same later cuts, which is the locality the rule promises.
        let first_cut = usize::from(
            full.first()
                .expect("the corpus produces at least one span")
                .end(),
        );
        let suffix = &records[first_cut ..];
        let recut = leaf_spans(suffix, params).expect("the suffix encodes");

        let shifted: Vec<usize> = full
            .as_ref()
            .iter()
            .skip(1_usize)
            .map(|span| usize::from(span.end()).saturating_sub(first_cut))
            .collect();
        let direct: Vec<usize> = recut
            .as_ref()
            .iter()
            .map(|span| usize::from(span.end()))
            .collect();

        assert_eq!(shifted, direct);
    }

    #[test]
    fn empty_records_are_admissible_input_to_the_rule()
    {
        let records = vec![RecordRef::new(b"".as_slice(), b"".as_slice())];
        let spans = leaf_spans(records.as_slice(), BoundaryParams::current())
            .expect("an empty record encodes");

        assert_eq!(spans.len(), 1_usize);
    }
}
