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
//! The rule is the chunker's typed boundary scanner in its degenerate
//! instance: every record is one boundary event of one token, and its residue
//! is the leading eight bytes, little-endian, of the digest of its canonical
//! encoding under the boundary domain. Kappa is two to the
//! [`BoundaryMaskBits`] power, so a record ends a leaf when its residue has
//! that many low zero bits — a decision that reads one record and nothing
//! else. The token cap is the [`BoundaryRecordCap`], which ends a leaf the
//! digest has not ended and so bounds leaf size, at the cost of making the cut
//! position-dependent inside one capped run: an edit can move a capped cut,
//! but only within the run it falls in, never past the next digest-induced
//! cut.
//!
//! The parameters are protocol constants, not tuning knobs: two writers that
//! disagree on them build different trees from the same records. They are
//! therefore committed — [`BoundaryParams::commitment`] goes into the hashed
//! root manifest, so a root states the rule its leaves were cut by.

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::fmt;
use core::num::NonZeroU64;

use anodized::spec;
use gandr_storage_chunker::BoundaryEvent;
use gandr_storage_chunker::BoundaryResidue;
use gandr_storage_chunker::CutDecision;
use gandr_storage_chunker::Kappa;
use gandr_storage_chunker::TokenCap;
use gandr_storage_chunker::TokenCount;
use gandr_storage_chunker::TypedChunker;
use gandr_storage_chunker::TypedChunkerParams;

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
///
/// # Specification
/// - requires: nothing.
/// - ensures: safe construction admits widths from one through thirty-two
///   inclusive and preserves the offered width.
/// - fails: outside widths are refused by the checked conversion.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 exhausts all 256 input bytes and observes refinement
///   admission, the exact converted width or its refusal class. Shifted bounds
///   and substituted widths are distinguished.
/// - witness: `boundary::tests::mask_bits_admit_the_interval_and_refuse_outside`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[spec(maintains: self.0 >= 1_u8 && self.0 <= 32_u8)]
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
    /// - hypothesis: L3 exhausts all input bytes against the interval 1..=32,
    ///   observing preserved widths or the refusal class. Shifted bounds, lost
    ///   values and wrong error classes are distinguished.
    /// - witness: `boundary::tests::mask_bits_admit_the_interval_and_refuse_outside`
    #[inline]
    #[spec(ensures: |ret| match ret.as_ref() {
        Ok(width) => (Self::MIN.0..=Self::MAX.0).contains(&bits) && width.0 == bits,
        Err(error) => !(Self::MIN.0..=Self::MAX.0).contains(&bits)
            && matches!(error, &RecordTreeError::IncompatibleParameters { .. }),
    })]
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
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on the width endpoints and caps 1, 37 and `u32::MAX`
    ///   compares padded rendering with the carried primitive; L3 observes sink
    ///   refusal. Substituted values, ignored flags and swallowed errors are
    ///   distinguished.
    /// - witness: `boundary::tests::parameter_formatting_preserves_values_and_refusal`
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
///
/// # Specification
/// - requires: nothing.
/// - ensures: safe construction admits exactly the positive u32 counts and
///   preserves the offered cap.
/// - fails: zero is refused by the checked conversion.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 at zero, one, 65 and `u32::MAX` observes refinement
///   admission and the refusal class or exact converted cap, distinguishing
///   zero admission, premature ceilings and truncation.
/// - witness: `boundary::tests::record_cap_refuses_zero`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[spec(maintains: self.0 > 0_u32)]
pub struct BoundaryRecordCap(u32);

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
    /// - hypothesis: L3 at zero, one, 65 and `u32::MAX` observes the refusal
    ///   class or preserved cap, distinguishing zero admission, premature
    ///   ceilings and truncation.
    /// - witness: `boundary::tests::record_cap_refuses_zero`
    #[inline]
    #[spec(ensures: |ret| match ret.as_ref() {
        Ok(limit) => cap != 0 && limit.0 == cap,
        Err(error) => cap == 0
            && matches!(error, &RecordTreeError::IncompatibleParameters { .. }),
    })]
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
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on the width endpoints and caps 1, 37 and `u32::MAX`
    ///   compares padded rendering with the carried primitive; L3 observes sink
    ///   refusal. Substituted values, ignored flags and swallowed errors are
    ///   distinguished.
    /// - witness: `boundary::tests::parameter_formatting_preserves_values_and_refusal`
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 on the default and wide-cap commitments observes the
    ///   leading protocol byte, distinguishing changed discriminators without
    ///   relying on enum ordinal position.
    /// - witness: `boundary::tests::default_commitment_is_pinned`
    /// - witness: `boundary::tests::commitment_preserves_wide_caps`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.0 == 1)]
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
///   can hash.
/// - fails: never, once constructed.
/// - panics: none.
/// - executable: none — every admitted component combination is valid. Equality
///   of commitments relates two parameter sets, not one; `commitment` checks
///   each returned image against its fields.
///
/// # Adequacy
/// - hypothesis: L2 compares default and wide-cap wire images with literal
///   goldens; L3 varies mask 4/5 and cap 64/65 independently. Missing fields,
///   swapped fields and narrowing are distinguished. The profile enum has only
///   one variant, so a profile perturbation is not available.
/// - witness: `boundary::tests::default_commitment_is_pinned`
/// - witness: `boundary::tests::each_field_moves_the_commitment`
/// - witness: `boundary::tests::commitment_preserves_wide_caps`
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
    /// - requires: nothing beyond the component types' checked invariants.
    /// - ensures: the set carries exactly the three choices offered.
    /// - provides: the only way to state a boundary rule, so a rule is always
    ///   three deliberate choices.
    /// - fails: never — the range checks live in the two conversions.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 observes exact default and explicit wide-cap wire
    ///   images; L3 varies mask and cap independently, distinguishing dropped
    ///   or substituted choices.
    /// - witness: `boundary::tests::commitment_preserves_wide_caps`
    /// - witness: `boundary::tests::each_field_moves_the_commitment`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.mask_bits.0 == mask_bits.0
        && ret.record_cap.0 == record_cap.0)]
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 observes the current rule's committed wire bytes and
    ///   its cut positions over 200 records, distinguishing changed defaults or
    ///   changed boundary semantics.
    /// - witness: `boundary::tests::default_commitment_is_pinned`
    /// - witness: `boundary::tests::the_cuts_of_a_fixed_corpus_are_pinned`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.mask_bits.0 == 4 && ret.record_cap.0 == 64)]
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 compares default and mixed-byte cap images with literal
    ///   goldens; L3 varies each variable field independently. Reordering,
    ///   omitted fields, endianness changes and cap truncation are
    ///   distinguished.
    /// - witness: `boundary::tests::default_commitment_is_pinned`
    /// - witness: `boundary::tests::commitment_preserves_wide_caps`
    /// - witness: `boundary::tests::each_field_moves_the_commitment`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.as_ref().iter().copied().eq(
        [u8::from(self.profile.tag()), u8::from(self.mask_bits)].into_iter()
            .chain(u64::from(u32::from(self.record_cap)).to_le_bytes()),
    ))]
    pub fn commitment(&self) -> ProfileCommitment
    {
        let mut bytes = WireBuffer::new();
        bytes.push_tag(self.profile.tag());
        bytes.push_tag(WireTag::from(u8::from(self.mask_bits)));
        bytes.push_long(WireLong::from(u64::from(u32::from(self.record_cap))));

        ProfileCommitment::from(Vec::<u8>::from(bytes))
    }

    /// Returns the typed-scanner rule these parameters are the degenerate
    /// instance of: kappa two to the mask width, and the record cap as the
    /// token cap.
    ///
    /// # Specification
    /// - requires: the component invariants hold: the mask width is between one
    ///   and thirty-two inclusive, and the record cap is at least one.
    /// - ensures: `|ret| u64::from(ret.kappa()).is_power_of_two() &&
    ///   u64::from(ret.kappa()).trailing_zeros() == u32::from(self.mask_bits.0)
    ///   && u64::from(ret.cap()) == u64::from(self.record_cap.0)` — kappa is
    ///   exactly two to the mask width and the cap is exactly the record cap,
    ///   so a residue is divisible by kappa when its masked bits are all zero.
    /// - provides: the rule the span walk drives the scanner with.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 at mask widths 1, 4 and 32 and caps 1, 64 and
    ///   `u32::MAX` observes exact kappa/cap pairs. Wrong exponents, off-by-one
    ///   caps and saturation are distinguished.
    /// - witness: `boundary::tests::the_scanner_rule_is_two_to_the_width_and_the_cap`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| u64::from(ret.kappa()).is_power_of_two()
        && u64::from(ret.kappa()).trailing_zeros() == u32::from(self.mask_bits.0)
        && u64::from(ret.cap()) == u64::from(self.record_cap.0))]
    fn scanner_params(self) -> TypedChunkerParams
    {
        // Both forms are exact on minted parameters: two to at most the
        // thirty-second power fits sixty-four bits, and a cap of at least one
        // is one plus its predecessor. Neither saturates.
        let two = NonZeroU64::MIN.saturating_add(1_u64);
        let kappa = two.saturating_pow(u32::from(self.mask_bits.0));
        let cap =
            NonZeroU64::MIN.saturating_add(u64::from(self.record_cap.0).saturating_sub(1_u64));

        TypedChunkerParams::new(Kappa::from(kappa), TokenCap::from(cap))
    }

    /// Returns the residue the scanner reads for one record.
    ///
    /// # Specification
    /// - requires: `record` is the canonical encoding of one record.
    /// - ensures: the leading eight bytes of the record's digest under the
    ///   boundary domain, read little-endian.
    /// - provides: the boundary event's residue, determined by this record
    ///   rather than any preceding or following record.
    /// - fails: none — the residue is total.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 compares cut positions for 200 records under the
    ///   current and mixed cap/digest rules with fixed expectations; L3 re-cuts
    ///   an aligned suffix. Enforcing calls also compare every residue byte
    ///   with the digest. Wrong hashing domains, byte order, digest windows and
    ///   predecessor dependence are distinguished on that corpus.
    /// - witness: `boundary::tests::the_cuts_of_a_fixed_corpus_are_pinned`
    /// - witness: `boundary::tests::a_records_decision_reads_only_that_record`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| digest(Domain::Boundary, WireBytes::from(record.as_ref()))
        .as_ref().get(..8) == Some(u64::from(ret).to_le_bytes().as_slice()))]
    fn residue(
        self,
        record: RecordEncoding<'_>,
    ) -> BoundaryResidue
    {
        match self.profile {
            | BoundaryProfile::RecordDigest => {
                let hash = digest(Domain::Boundary, WireBytes::from(record.as_ref()));
                let mut leading = [0_u8; 8_usize];
                let (head, _tail) = hash.as_ref().split_at(leading.len());
                leading.copy_from_slice(head);

                BoundaryResidue::from(u64::from_le_bytes(leading))
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 observes the default rule's exact committed bytes,
    ///   distinguishing divergence from the current protocol profile.
    /// - witness: `boundary::tests::default_commitment_is_pinned`
    #[inline]
    #[spec(ensures: |ret| ret == Self::current())]
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
    /// - requires: nothing.
    /// - ensures: owns the offered byte sequence without adding or removing
    ///   bytes.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on default and mixed-byte cap commitments observes the
    ///   complete image, distinguishing omitted, reordered or substituted
    ///   bytes.
    /// - witness: `boundary::tests::default_commitment_is_pinned`
    /// - witness: `boundary::tests::commitment_preserves_wide_caps`
    #[inline]
    #[spec(captures: offered = (bytes.len(), bytes.first().copied(), bytes.last().copied()),
        ensures: |ret| (ret.as_ref().len(), ret.as_ref().first().copied(),
            ret.as_ref().last().copied()) == offered)]
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

/// A half-open run of record positions forming one leaf.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the start does not exceed the end; emitted nonempty leaves cover
///   a contiguous run, while the empty constructor denotes 0..0.
/// - fails: never, once constructed.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 on empty, one-record and 500-record inputs observes exact
///   endpoints and contiguous coverage; a privately reversed span has a false
///   refinement. Reversed runs, skipped positions and nonempty representations
///   of the empty leaf are distinguished.
/// - witness: `boundary::tests::spans_partition_the_input`
/// - witness: `boundary::tests::empty_records_are_admissible_input_to_the_rule`
/// - witness: `tests::build::an_empty_tree_is_one_empty_leaf`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[spec(maintains: self.start <= self.end)]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 builds an empty tree and observes one empty leaf and
    ///   zero committed records, distinguishing a shifted or nonempty run.
    /// - witness: `tests::build::an_empty_tree_is_one_empty_leaf`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| matches!((ret.start, ret.end),
        (RecordIndex::ZERO, RecordIndex::ZERO)))]
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
/// - ensures: the record domain tag followed by the key length, key bytes,
///   value length and value bytes, with both lengths as little-endian u64s.
///   Decoding this complete image recovers the offered pair, so distinct pairs
///   cannot share an encoding.
/// - provides: the boundary rule's input outside a node encoding.
/// - fails: [`RecordTreeError::ArithmeticOverflow`] when a key or value length
///   exceeds the wire width.
/// - panics: none.
///
/// # Errors
/// [`RecordTreeError::ArithmeticOverflow`] — a field length exceeds `u64`.
///
/// # Adequacy
/// - hypothesis: L2 on empty fields and a mixed binary pair compares full wire
///   images with literal goldens; L3 separates (ab, c) from (a, bc). Missing
///   lengths, swapped fields, wrong domains and trailing bytes are
///   distinguished. Wider-than-u64 field lengths are not constructible on the
///   supported targets.
/// - witness: `boundary::tests::record_encoding_separates_the_ambiguity_pair`
/// - witness: `boundary::tests::record_encoding_pins_field_framing`
#[spec(ensures: |ret| {
    let lengths_fit = u64::try_from(record.key().as_ref().len()).is_ok()
        && u64::try_from(record.value().as_ref().len()).is_ok();
    ret.is_ok() == lengths_fit && ret.as_ref().map_or_else(
        |error| matches!(error, &RecordTreeError::ArithmeticOverflow { .. }),
        |encoded| {
            let mut cursor = crate::wire::Cursor::new(WireBytes::from(encoded.as_ref()));
            cursor.expect_domain(Domain::Record, "record domain".into()).is_ok()
                && cursor.read_length_prefixed("record key".into())
                    .is_ok_and(|field| field.as_ref() == record.key().as_ref())
                && cursor.read_length_prefixed("record value".into())
                    .is_ok_and(|field| field.as_ref() == record.value().as_ref())
                && cursor.completion() == crate::wire::DecodeCompletion::Complete
        },
    )
})]
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
/// - intension: excluding executable predicates, exactly one pass over
///   `records`, one record encoding, one digest and one scanner step per
///   record, with no lookahead. Returned partitions observe boundary locality
///   but do not measure these operational counts.
///
/// # Errors
/// [`RecordTreeError::ArithmeticOverflow`] — a record's fields or a position
/// exceed their widths.
///
/// # Adequacy
/// - hypothesis: L2 observes a complete partition of 500 records and fixed cut
///   positions for 200 records under current and mixed rules; L3 observes eight
///   cap-length runs of eight, an empty input and one empty record. Gaps,
///   overlap, omitted tails, skipped empty records, wrong digest rules and
///   disabled cap cuts are distinguished on these corpora. Exact work counts
///   and absence of speculative reads remain unmeasured by this suite.
/// - witness: `boundary::tests::spans_partition_the_input`
/// - witness: `boundary::tests::the_cuts_of_a_fixed_corpus_are_pinned`
/// - witness: `boundary::tests::the_cap_ends_a_run_the_digest_does_not`
/// - witness: `boundary::tests::an_empty_input_has_no_spans`
/// - witness: `boundary::tests::empty_records_are_admissible_input_to_the_rule`
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
    let mut scanner = TypedChunker::new(&params.scanner_params());
    let mut start = RecordIndex::ZERO;
    let mut position = RecordIndex::ZERO;

    for record in records {
        let encoded = encode_record(*record)?;
        position = position.next()?;

        // Every record is one boundary event of one token, so the scanner's
        // pending count is the run length and its cap the record cap.
        let event = BoundaryEvent::new(TokenCount::ONE, params.residue(encoded.as_borrowed()));

        if let CutDecision::Cut(_reason) = scanner.on_boundary(event) {
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
    use super::RecordSpan;
    use super::encode_record;
    use super::leaf_spans;
    use crate::bytes::OwnedRecordEncoding;
    use crate::bytes::RecordEncoding;
    use crate::error::RecordTreeError;
    use crate::record::Record;
    use crate::record::RecordCount;
    use crate::record::RecordIndex;
    use crate::record::RecordRef;

    /// A corpus of `count` records with distinct keys in key order.
    ///
    /// # Specification
    /// - requires: `count` is at most 100,000,000, so every position fits the
    ///   eight-digit key field and numeric order agrees with byte order.
    /// - ensures: exactly `count` records with keys `key-{index:08}` and values
    ///   `value-{index:08}`, in increasing position order.
    /// - provides: the corpus every span fixture below is cut from, ordered so
    ///   a test never depends on the build's own sorting.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on corpora of 64, 200 and 500 records observes exact
    ///   partitions and fixed cut positions. Dropped records, duplicate keys
    ///   and changed fixture bytes are distinguished on these corpora.
    /// - witness: `boundary::tests::spans_partition_the_input`
    /// - witness: `boundary::tests::the_cuts_of_a_fixed_corpus_are_pinned`
    #[anodized::spec(requires: u64::from(count) <= 100_000_000,
        ensures: |ret| u64::try_from(ret.len()) == Ok(u64::from(count))
            && ret.array_windows::<2>().all(|pair| pair[0].key() < pair[1].key()))]
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 on 200- and 500-record corpora observes exact coverage
    ///   and fixed cut positions. Dropped, duplicated or permuted records
    ///   change those observers.
    /// - witness: `boundary::tests::spans_partition_the_input`
    /// - witness: `boundary::tests::the_cuts_of_a_fixed_corpus_are_pinned`
    #[anodized::spec(ensures: |ret| ret.iter().copied()
        .eq(records.iter().map(Record::as_record_ref)))]
    fn borrow(records: &[Record]) -> Vec<RecordRef<'_>>
    {
        records.iter().map(Record::as_record_ref).collect()
    }

    #[test]
    fn mask_bits_admit_the_interval_and_refuse_outside()
    {
        for bits in 0_u8 ..= u8::MAX {
            assert_eq!(
                anodized::types::Spec::predicate(&BoundaryMaskBits(bits)),
                (1_u8 ..= 32).contains(&bits)
            );
            let converted = BoundaryMaskBits::try_from(bits);
            if (1_u8 ..= 32).contains(&bits) {
                assert_eq!(converted.map(u8::from), Ok(bits));
            }
            else {
                assert!(matches!(
                    converted,
                    Err(RecordTreeError::IncompatibleParameters { .. })
                ));
            }
        }
    }

    #[test]
    fn record_cap_refuses_zero()
    {
        assert!(!anodized::types::Spec::predicate(&BoundaryRecordCap(0_u32)));
        assert!(matches!(
            BoundaryRecordCap::try_from(0_u32),
            Err(RecordTreeError::IncompatibleParameters { .. })
        ));
        for cap in [1_u32, 65, u32::MAX] {
            assert!(anodized::types::Spec::predicate(&BoundaryRecordCap(cap)));
            assert_eq!(BoundaryRecordCap::try_from(cap).map(u32::from), Ok(cap));
        }
    }

    #[test]
    fn the_scanner_rule_is_two_to_the_width_and_the_cap()
    {
        let rule = |bits: BoundaryMaskBits, cap: u32| {
            let params = BoundaryParams::new(
                BoundaryProfile::CURRENT,
                bits,
                BoundaryRecordCap::try_from(cap).expect("a fixture cap is admissible"),
            )
            .scanner_params();
            (u64::from(params.kappa()), u64::from(params.cap()))
        };

        // Both ends of each range: the narrowest and widest widths, and the
        // smallest and largest caps, none of which may saturate.
        assert_eq!(rule(BoundaryMaskBits::MIN, 1_u32), (2_u64, 1_u64));
        assert_eq!(
            rule(BoundaryMaskBits::MAX, u32::MAX),
            (1_u64 << 32_u32, u64::from(u32::MAX))
        );
        assert_eq!(
            rule(BoundaryParams::current().mask_bits(), 64_u32),
            (16_u64, 64_u64)
        );
    }

    #[test]
    fn default_commitment_is_pinned()
    {
        let commitment = BoundaryParams::default().commitment();

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
            assert!(anodized::types::Spec::predicate(span));
            assert_eq!(usize::from(span.start()), expected_start);
            assert!(usize::from(span.end()) > usize::from(span.start()));
            expected_start = usize::from(span.end());
        }
        assert_eq!(expected_start, records.len());
        assert!(spans.len() > 1_usize, "the corpus produces several leaves");
        assert!(anodized::types::Spec::predicate(&RecordSpan::empty()));
        assert!(!anodized::types::Spec::predicate(&RecordSpan {
            start: RecordIndex::from(1_usize),
            end: RecordIndex::ZERO,
        }));
    }

    #[test]
    fn the_cap_ends_a_run_the_digest_does_not()
    {
        let owned = corpus(RecordCount::from(64_u64));
        let records = borrow(owned.as_slice());
        // This fixed corpus has no digest-induced cut under the wide mask;
        // exact cap-length runs distinguish the cap from the digest rule.
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

        assert!(
            spans
                .iter()
                .map(|span| (usize::from(span.start()), usize::from(span.end())))
                .eq([(0_usize, 1_usize)])
        );
    }

    #[test]
    fn the_cuts_of_a_fixed_corpus_are_pinned()
    {
        let owned = corpus(RecordCount::from(200_u64));
        let records = borrow(owned.as_slice());
        let ends = |params: BoundaryParams| -> Vec<usize> {
            leaf_spans(records.as_slice(), params)
                .expect("the corpus encodes")
                .iter()
                .map(|span| usize::from(span.end()))
                .collect()
        };
        // A one-bit mask under a cap of three mixes digest cuts with cap cuts,
        // so the pin covers both causes and their interaction.
        let mixed = BoundaryParams::new(
            BoundaryProfile::CURRENT,
            BoundaryMaskBits::MIN,
            BoundaryRecordCap::try_from(3_u32).expect("three is admissible"),
        );

        // Where leaves end is protocol: these positions are what every root
        // built under these parameters commits to.
        assert_eq!(ends(BoundaryParams::current()), vec![
            12, 55, 64, 97, 100, 139, 144, 160, 165, 175, 200
        ]);
        let mixed_ends = ends(mixed);
        assert_eq!(mixed_ends.len(), 112_usize);
        assert_eq!(mixed_ends[.. 25_usize], [
            1, 4, 6, 9, 10, 12, 15, 16, 17, 18, 19, 21, 22, 23, 24, 26, 27, 28, 30, 33, 36, 38, 39,
            41, 43
        ]);
    }

    #[test]
    fn commitment_preserves_wide_caps()
    {
        let params = BoundaryParams::new(
            BoundaryProfile::CURRENT,
            BoundaryMaskBits::MAX,
            BoundaryRecordCap::try_from(0x0102_0304_u32).expect("the cap is positive"),
        );
        assert_eq!(params.commitment().as_ref(), [
            1_u8, 32, 4, 3, 2, 1, 0, 0, 0, 0
        ]);
    }

    #[test]
    fn record_encoding_pins_field_framing()
    {
        let empty = b"gandr:storage-records:record:v1\
            \0\0\0\0\0\0\0\0\
            \0\0\0\0\0\0\0\0";
        let binary = b"gandr:storage-records:record:v1\
            \x02\0\0\0\0\0\0\0\0\xff\
            \x03\0\0\0\0\0\0\0\x80\x01\0";
        let pair = b"gandr:storage-records:record:v1\
            \x02\0\0\0\0\0\0\0ab\
            \x01\0\0\0\0\0\0\0c";
        // Independent BLAKE3 vectors pin the boundary domain and byte order.
        let cases = [
            (
                RecordRef::new(b"", b""),
                OwnedRecordEncoding::from(empty),
                9_148_802_485_720_952_849_u64,
            ),
            (
                RecordRef::new(b"\0\xff", b"\x80\x01\0"),
                OwnedRecordEncoding::from(binary.as_slice()),
                10_278_879_429_000_478_782_u64,
            ),
            (
                RecordRef::new(b"ab", b"c"),
                OwnedRecordEncoding::from(RecordEncoding::from(pair)),
                18_332_636_201_592_727_709_u64,
            ),
        ];
        let params = BoundaryParams::current();
        for (record, image, residue) in cases {
            assert_eq!(encode_record(record).expect("the fields fit"), image);
            assert_eq!(u64::from(params.residue(image.as_borrowed())), residue);
        }
    }

    /// A sink that refuses every offered byte sequence.
    struct RefusingSink;

    impl core::fmt::Write for RefusingSink
    {
        /// Refuses a formatter write.
        ///
        /// # Specification
        /// - requires: nothing.
        /// - ensures: returns the formatter error for every offered string.
        /// - fails: always with the formatter error.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L3 observes the sink refusal through both parameter
        ///   formatters, distinguishing swallowed or converted refusals.
        /// - witness: `boundary::tests::parameter_formatting_preserves_values_and_refusal`
        #[anodized::spec(ensures: |ret| ret == Err(core::fmt::Error))]
        fn write_str(
            &mut self,
            _text: &str,
        ) -> core::fmt::Result
        {
            Err(core::fmt::Error)
        }
    }

    #[test]
    fn parameter_formatting_preserves_values_and_refusal()
    {
        for offered in [1_u8, 32] {
            let width = BoundaryMaskBits::try_from(offered).expect("the width is admissible");
            assert_eq!(
                alloc::format!("{width:0>12}"),
                alloc::format!("{offered:0>12}")
            );
            assert_eq!(
                core::fmt::Write::write_fmt(&mut RefusingSink, format_args!("{width}")),
                Err(core::fmt::Error)
            );
        }
        for offered in [1_u32, 37, u32::MAX] {
            let cap = BoundaryRecordCap::try_from(offered).expect("the cap is admissible");
            assert_eq!(
                alloc::format!("{cap:0>12}"),
                alloc::format!("{offered:0>12}")
            );
            assert_eq!(
                core::fmt::Write::write_fmt(&mut RefusingSink, format_args!("{cap}")),
                Err(core::fmt::Error)
            );
        }
    }
}
