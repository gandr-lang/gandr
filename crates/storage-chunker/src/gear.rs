//! The record-safe profile: a Gear scanner over canonical record bytes that
//! cuts only between complete records.
//!
//! # The rule
//!
//! Each chunk keeps a Gear state, reset at the chunk's first record to an
//! initial state derived from the committed seed policy. Every byte of every
//! record mixes into it: the state rotates left by one and adds the table's
//! value for the byte. After a complete record, the chunk ends when it has
//! reached the byte or record cap, or — once it has met both minimum limits —
//! when the state masked by the target's power-of-two mask is zero. The scan
//! reads each byte once and never looks ahead, so a cut a record induces
//! travels with that record's bytes.
//!
//! # The committed fields
//!
//! ```text
//! profile fields := u16le Gear table version
//!                || u8 seed kind || 32 salt bytes
//!                || u8 normalization policy || u8 record-boundary rule
//!                || u64le min bytes || u64le target bytes || u64le max bytes
//!                || u32le min records || u32le target records || u32le max records
//! ```
//!
//! # The Gear table
//!
//! The version-1 table is the first 256 outputs of `SplitMix64` seeded with
//! the first sixty-four fractional bits of the square root of two, built at
//! compile time from that statement rather than carried as a literal, so its
//! provenance is the code.

use alloc::vec::Vec;

use crate::commitment::AlgorithmVersion;
use crate::commitment::CommitmentField;
use crate::commitment::CommitmentWriter;
use crate::commitment::ParameterCommitment;
use crate::error::ArithmeticOperation;
use crate::error::ChunkerError;
use crate::error::InvalidParameterReason;
use crate::error::ProfileField;
use crate::error::RawDiscriminator;
use crate::span::BoundaryReason;
use crate::span::ByteSpan;
use crate::span::ChunkSpan;
use crate::span::RecordSpan;
use crate::units::ByteCount;
use crate::units::BytePosition;
use crate::units::RecordCount;
use crate::units::RecordPosition;

/// The number of entries in a Gear table: one per byte value.
const GEAR_TABLE_LEN: usize = 0x100_usize;

/// The seed of the version-1 Gear table: the first sixty-four fractional bits
/// of the square root of two.
const GEAR_TABLE_V1_SEED: u64 = 0x6A09_E667_F3BC_C909_u64;

/// The `SplitMix64` state increment: the sixty-four-bit golden-ratio constant.
const SPLITMIX_GAMMA: u64 = 0x9E37_79B9_7F4A_7C15_u64;

/// The first `SplitMix64` output multiplier.
const SPLITMIX_MIX_FIRST: u64 = 0xBF58_476D_1CE4_E5B9_u64;

/// The second `SplitMix64` output multiplier.
const SPLITMIX_MIX_SECOND: u64 = 0x94D0_49BB_1331_11EB_u64;

/// The state a chunk's Gear scan starts from before seed mixing: the first
/// sixty-four fractional bits of pi.
const GEAR_STATE_IV: u64 = 0x243F_6A88_85A3_08D3_u64;

/// The multiplier a salt byte is mixed into the initial state with.
const SEED_MIX_MULTIPLIER: u64 = 0x9E37_79B9_7F4A_7C15_u64;

/// The byte length of a public seed salt.
const SEED_SALT_LEN: usize = 0x20_usize;

/// A Gear table: one mixing value per byte value.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct GearTable([u64; GEAR_TABLE_LEN]);

/// The version-1 Gear table, built at compile time.
const GEAR_TABLE_V1: GearTable = gear_table_v1();

/// Builds the version-1 Gear table: `SplitMix64`'s first 256 outputs from
/// [`GEAR_TABLE_V1_SEED`].
///
/// # Specification
/// - requires: nothing.
/// - ensures: entry `n` is `SplitMix64`'s `n + 1`-th output from the seed — the
///   state advanced by `n + 1` increments, then the two xor-shift-multiply
///   rounds and a final xor-shift.
/// - provides: the table [`GearTableVersion::V1`] names, with its provenance
///   stated as code.
/// - fails: never.
/// - panics: none.
/// - executable: none — the pinned instrument cannot expand in this const
///   generator; retaining compile-time table construction is required.
///
/// # Adequacy
/// - hypothesis: L2 agreement against a pinned golden — entries at both ends
///   and in the middle are asserted equal to the published table they were
///   first carried as, so a changed seed, increment or mixing constant moves at
///   least one.
/// - witness: `gear::tests::the_v1_table_is_pinned`
const fn gear_table_v1() -> GearTable
{
    let mut table = [0_u64; GEAR_TABLE_LEN];
    let mut state = GEAR_TABLE_V1_SEED;
    let mut rest: &mut [u64] = &mut table;

    while let Some((slot, tail)) = rest.split_first_mut() {
        state = state.wrapping_add(SPLITMIX_GAMMA);
        let mut mixed = state;
        mixed = (mixed ^ (mixed >> 30_u32)).wrapping_mul(SPLITMIX_MIX_FIRST);
        mixed = (mixed ^ (mixed >> 27_u32)).wrapping_mul(SPLITMIX_MIX_SECOND);
        *slot = mixed ^ (mixed >> 31_u32);
        rest = tail;
    }

    GearTable(table)
}

/// The Gear table a record-safe profile mixes bytes with.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum GearTableVersion
{
    /// The `SplitMix64` table this module documents.
    V1,
}

impl GearTableVersion
{
    /// Returns the discriminator this table is committed under.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn discriminator(self) -> RawDiscriminator
    {
        match self {
            | Self::V1 => RawDiscriminator(0x0001_u16),
        }
    }
}

impl TryFrom<u16> for GearTableVersion
{
    type Error = ChunkerError;

    /// Reads a raw table version, refusing one this build does not carry.
    ///
    /// # Specification
    /// - requires: nothing; the value is arbitrary.
    /// - ensures: on success the version whose discriminator is `raw`.
    /// - provides: the only way from a raw value to a table version.
    /// - fails: [`ChunkerError::UnsupportedProfileValue`] naming the table
    ///   field and `raw` for any other value.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ChunkerError::UnsupportedProfileValue`] — `raw` names no table.
    ///
    /// # Adequacy
    /// - hypothesis: L3 over the complete 16-bit raw domain; exact variants,
    ///   field tags and raw payloads distinguish acceptance and error
    ///   mutations.
    /// - witness: `tests::commitment::raw_discriminators_round_trip_and_refuse_by_field`
    #[anodized::spec(ensures: |ret| ret == if raw == 1 {
        Ok(Self::V1)
    } else {
        Err(ChunkerError::UnsupportedProfileValue {
            field: ProfileField::GearTable, raw: RawDiscriminator::from(raw),
        })
    })]
    #[inline]
    fn try_from(raw: u16) -> Result<Self, Self::Error>
    {
        if raw == u16::from(Self::V1.discriminator()) {
            return Ok(Self::V1);
        }

        Err(ChunkerError::UnsupportedProfileValue {
            field: ProfileField::GearTable,
            raw: RawDiscriminator(raw),
        })
    }
}

/// How the scanner treats the bytes it is handed.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum NormalizationPolicy
{
    /// The bytes are already canonical and are scanned exactly as given.
    PreserveBytes,
}

impl NormalizationPolicy
{
    /// Returns the discriminator this policy is committed under.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn discriminator(self) -> RawDiscriminator
    {
        match self {
            | Self::PreserveBytes => RawDiscriminator(0x0000_u16),
        }
    }
}

impl TryFrom<u8> for NormalizationPolicy
{
    type Error = ChunkerError;

    /// Reads a raw normalization policy, refusing one this build does not
    /// implement.
    ///
    /// # Specification
    /// - requires: nothing; the value is arbitrary.
    /// - ensures: on success the policy whose discriminator is `raw`.
    /// - provides: the only way from a raw value to a policy.
    /// - fails: [`ChunkerError::UnsupportedProfileValue`] naming the
    ///   normalization field and `raw` for any other value.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ChunkerError::UnsupportedProfileValue`] — `raw` names no policy.
    ///
    /// # Adequacy
    /// - hypothesis: L3 over the complete 8-bit raw domain; exact variants,
    ///   field tags and raw payloads distinguish acceptance and error
    ///   mutations.
    /// - witness: `tests::commitment::raw_discriminators_round_trip_and_refuse_by_field`
    #[anodized::spec(ensures: |ret| ret == if raw == 0 {
        Ok(Self::PreserveBytes)
    } else {
        Err(ChunkerError::UnsupportedProfileValue {
            field: ProfileField::Normalization, raw: RawDiscriminator::from(raw),
        })
    })]
    #[inline]
    fn try_from(raw: u8) -> Result<Self, Self::Error>
    {
        if u16::from(raw) == u16::from(Self::PreserveBytes.discriminator()) {
            return Ok(Self::PreserveBytes);
        }

        Err(ChunkerError::UnsupportedProfileValue {
            field: ProfileField::Normalization,
            raw: RawDiscriminator::from(raw),
        })
    }
}

/// Where the scanner may place a cut.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum RecordBoundaryRule
{
    /// Only between two complete records.
    BetweenRecords,
}

impl RecordBoundaryRule
{
    /// Returns the discriminator this rule is committed under.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn discriminator(self) -> RawDiscriminator
    {
        match self {
            | Self::BetweenRecords => RawDiscriminator(0x0000_u16),
        }
    }
}

impl TryFrom<u8> for RecordBoundaryRule
{
    type Error = ChunkerError;

    /// Reads a raw record-boundary rule, refusing one this build does not
    /// implement.
    ///
    /// # Specification
    /// - requires: nothing; the value is arbitrary.
    /// - ensures: on success the rule whose discriminator is `raw`.
    /// - provides: the only way from a raw value to a rule.
    /// - fails: [`ChunkerError::UnsupportedProfileValue`] naming the rule field
    ///   and `raw` for any other value.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ChunkerError::UnsupportedProfileValue`] — `raw` names no rule.
    ///
    /// # Adequacy
    /// - hypothesis: L3 over the complete 8-bit raw domain; exact variants,
    ///   field tags and raw payloads distinguish acceptance and error
    ///   mutations.
    /// - witness: `tests::commitment::raw_discriminators_round_trip_and_refuse_by_field`
    #[anodized::spec(ensures: |ret| ret == if raw == 0 {
        Ok(Self::BetweenRecords)
    } else {
        Err(ChunkerError::UnsupportedProfileValue {
            field: ProfileField::RecordBoundaryRule, raw: RawDiscriminator::from(raw),
        })
    })]
    #[inline]
    fn try_from(raw: u8) -> Result<Self, Self::Error>
    {
        if u16::from(raw) == u16::from(Self::BetweenRecords.discriminator()) {
            return Ok(Self::BetweenRecords);
        }

        Err(ChunkerError::UnsupportedProfileValue {
            field: ProfileField::RecordBoundaryRule,
            raw: RawDiscriminator::from(raw),
        })
    }
}

/// A caller-chosen public salt mixed into every chunk's initial Gear state.
///
/// Public, not secret: it is committed in the clear, and it varies where cuts
/// fall between deployments rather than hiding them.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct SeedSalt([u8; SEED_SALT_LEN]);

impl From<[u8; SEED_SALT_LEN]> for SeedSalt
{
    /// Takes the salt bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: [u8; SEED_SALT_LEN]) -> Self
    {
        Self(bytes)
    }
}

impl AsRef<[u8]> for SeedSalt
{
    /// Borrows the salt bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        self.0.as_slice()
    }
}

/// How each chunk's initial Gear state is seeded.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum SeedPolicy
{
    /// No salt: the initial state is the fixed one every deployment shares.
    Unsalted,
    /// A public salt is mixed into the initial state.
    PublicSalt(SeedSalt),
}

impl SeedPolicy
{
    /// Returns the seed-kind byte this policy is committed under.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn discriminator(&self) -> RawDiscriminator
    {
        match *self {
            | Self::Unsalted => RawDiscriminator(0x0000_u16),
            | Self::PublicSalt(_) => RawDiscriminator(0x0001_u16),
        }
    }

    /// Returns the committed salt bytes: the salt itself, or all zeroes for
    /// [`SeedPolicy::Unsalted`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn salt(&self) -> SeedSalt
    {
        match *self {
            | Self::Unsalted => SeedSalt([0_u8; SEED_SALT_LEN]),
            | Self::PublicSalt(salt) => salt,
        }
    }
}

/// The validated byte and record limits of a record-safe scan.
///
/// # Specification
/// - requires: nothing; explicit limits are validated and defaults are valid.
/// - ensures: every limit is non-zero, `min <= target <= max` holds for bytes
///   and for records, and the target byte limit is at most `u32::MAX`.
/// - provides: limits a scan can rely on without re-checking.
/// - fails: never, once constructed.
/// - panics: none.
/// - executable: none — this type-wide invariant is enforced by the executable
///   predicate on its validating constructor.
///
/// # Adequacy
/// - hypothesis: L3 over arbitrary six-field inputs; exact field values and
///   refusal reasons separate zero, order, width and precedence mutations.
/// - witness: `tests::gear::invalid_limits_are_refused_by_reason`
/// - witness: `tests::gear::equal_limits_are_admitted`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ChunkLimits
{
    /// Bytes a chunk must reach before the hash predicate may cut it.
    min_bytes: ByteCount,
    /// Bytes the cut mask is derived from.
    target_bytes: ByteCount,
    /// Bytes no chunk may exceed.
    max_bytes: ByteCount,
    /// Records a chunk must reach before the hash predicate may cut it.
    min_records: RecordCount,
    /// Records the profile commits as its target.
    target_records: RecordCount,
    /// Records no chunk may exceed.
    max_records: RecordCount,
}

impl ChunkLimits
{
    /// Validates a set of limits.
    ///
    /// # Specification
    /// - requires: nothing; the limits are arbitrary.
    /// - ensures: on success the limits carry exactly the six values offered.
    /// - provides: validation of arbitrary inputs before a scan trusts them.
    /// - fails: [`ChunkerError::InvalidParameters`] with the first refused
    ///   condition, checked in this order: a zero byte limit, a zero record
    ///   limit, a minimum byte limit over the target, a target byte limit over
    ///   the maximum, a target byte limit over `u32::MAX`, and record limits
    ///   out of order.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ChunkerError::InvalidParameters`] — the reason names the refused
    /// condition.
    ///
    /// # Adequacy
    /// - hypothesis: L3 only — each comparison is separated by its boundary
    ///   pair: a zero against a one in each position, equal limits (admitted)
    ///   against limits one apart in the wrong order (refused), and a target of
    ///   exactly `u32::MAX` against one past it.
    /// - witness: `tests::gear::invalid_limits_are_refused_by_reason`
    /// - witness: `tests::gear::equal_limits_are_admitted`
    #[anodized::spec(ensures: |ret| match ret {
        Ok(limits) => {
            limits.min_bytes == min_bytes && limits.target_bytes == target_bytes
                && limits.max_bytes == max_bytes && limits.min_records == min_records
                && limits.target_records == target_records && limits.max_records == max_records
                && min_bytes > ByteCount::ZERO && min_bytes <= target_bytes
                && target_bytes <= max_bytes && u32::try_from(u64::from(target_bytes)).is_ok()
                && min_records > RecordCount::ZERO && min_records <= target_records
                && target_records <= max_records
        }
        Err(error) => {
            let reason = if min_bytes == ByteCount::ZERO || target_bytes == ByteCount::ZERO || max_bytes == ByteCount::ZERO {
                Some(InvalidParameterReason::ZeroByteLimit)
            } else if min_records == RecordCount::ZERO || target_records == RecordCount::ZERO || max_records == RecordCount::ZERO {
                Some(InvalidParameterReason::ZeroRecordLimit)
            } else if min_bytes > target_bytes { Some(InvalidParameterReason::MinByteExceedsTargetByte) }
            else if target_bytes > max_bytes { Some(InvalidParameterReason::InvertedByteLimits) }
            else if u64::from(target_bytes) > u64::from(u32::MAX) { Some(InvalidParameterReason::TargetByteExceedsU32) }
            else if min_records > target_records || target_records > max_records { Some(InvalidParameterReason::InvertedRecordLimits) }
            else { None };
            reason.is_some_and(|reason| error == ChunkerError::InvalidParameters { reason })
        }
    })]
    #[inline]
    pub fn new(
        min_bytes: ByteCount,
        target_bytes: ByteCount,
        max_bytes: ByteCount,
        min_records: RecordCount,
        target_records: RecordCount,
        max_records: RecordCount,
    ) -> Result<Self, ChunkerError>
    {
        let zero_bytes = ByteCount::ZERO;
        let zero_records = RecordCount::ZERO;
        let widest_target = ByteCount::from(u64::from(u32::MAX));

        let reason =
            if min_bytes == zero_bytes || target_bytes == zero_bytes || max_bytes == zero_bytes {
                InvalidParameterReason::ZeroByteLimit
            }
            else if min_records == zero_records
                || target_records == zero_records
                || max_records == zero_records
            {
                InvalidParameterReason::ZeroRecordLimit
            }
            else if min_bytes > target_bytes {
                InvalidParameterReason::MinByteExceedsTargetByte
            }
            else if target_bytes > max_bytes {
                InvalidParameterReason::InvertedByteLimits
            }
            else if target_bytes > widest_target {
                InvalidParameterReason::TargetByteExceedsU32
            }
            else if min_records > target_records || target_records > max_records {
                InvalidParameterReason::InvertedRecordLimits
            }
            else {
                return Ok(Self {
                    min_bytes,
                    target_bytes,
                    max_bytes,
                    min_records,
                    target_records,
                    max_records,
                });
            };

        Err(ChunkerError::InvalidParameters { reason })
    }

    /// Returns the default limits: chunks of 4 KiB to 64 KiB around a 16 KiB
    /// target, and of 1 to 1024 records around a target of 64.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn default_fastcdc() -> Self
    {
        Self {
            min_bytes: ByteCount::from(0x1000_u64),
            target_bytes: ByteCount::from(0x4000_u64),
            max_bytes: ByteCount::from(0x0001_0000_u64),
            min_records: RecordCount::from(1_u32),
            target_records: RecordCount::from(0x40_u32),
            max_records: RecordCount::from(0x0400_u32),
        }
    }

    /// Returns the bytes a chunk must reach before the hash predicate may cut.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn min_bytes(&self) -> ByteCount
    {
        self.min_bytes
    }

    /// Returns the bytes the cut mask is derived from.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn target_bytes(&self) -> ByteCount
    {
        self.target_bytes
    }

    /// Returns the bytes no chunk may exceed.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn max_bytes(&self) -> ByteCount
    {
        self.max_bytes
    }

    /// Returns the records a chunk must reach before the hash predicate may
    /// cut.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn min_records(&self) -> RecordCount
    {
        self.min_records
    }

    /// Returns the committed target record count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn target_records(&self) -> RecordCount
    {
        self.target_records
    }

    /// Returns the records no chunk may exceed.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn max_records(&self) -> RecordCount
    {
        self.max_records
    }
}

impl Default for ChunkLimits
{
    /// Returns [`ChunkLimits::default_fastcdc`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self::default_fastcdc()
    }
}

/// A chunk-local Gear state.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct GearState(u64);

/// The mask the Gear state is tested against.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct CutMask(u64);

/// The parameters of the record-safe profile.
///
/// # Specification
/// - requires: nothing beyond what [`ChunkLimits::new`] enforces.
/// - ensures: two parameter sets are equal exactly when their commitments are
///   equal, because the commitment encodes every field and nothing else.
/// - provides: the rule a record-safe scan cuts by, in a form a downstream root
///   can bind.
/// - fails: never, once constructed.
/// - panics: none.
/// - executable: none — injectivity relates two independently constructed
///   parameter sets; the commitment method checks each concrete image.
///
/// # Adequacy
/// - hypothesis: L2 agreement — the default profile's commitment is a pinned
///   golden written out field by field — and L3 for the claim that each field
///   moves the commitment, one boundary pair per field.
/// - witness: `tests::commitment::the_default_record_safe_commitment_is_pinned`
/// - witness: `tests::commitment::each_record_safe_field_moves_the_commitment`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ChunkerParams
{
    /// The Gear table bytes are mixed with.
    gear_table: GearTableVersion,
    /// How each chunk's initial state is seeded.
    seed_policy: SeedPolicy,
    /// How the input bytes are treated.
    normalization: NormalizationPolicy,
    /// Where a cut may fall.
    record_boundary_rule: RecordBoundaryRule,
    /// The validated limits.
    limits: ChunkLimits,
}

impl ChunkerParams
{
    /// Assembles a record-safe profile from explicit choices.
    ///
    /// # Specification
    /// - requires: nothing beyond the invariant carried by `limits`.
    /// - ensures: the profile carries exactly the five choices offered.
    /// - provides: a record-safe profile assembled from five deliberate
    ///   choices.
    /// - fails: never — validation lives in the limits and the conversions.
    /// - panics: none.
    /// - executable: none — the pinned instrument cannot expand in this const
    ///   constructor without breaking const callers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on the default profile's exact committed image and L3
    ///   on independent field changes distinguish omission and substitution.
    /// - witness: `tests::commitment::the_default_record_safe_commitment_is_pinned`
    /// - witness: `tests::commitment::each_record_safe_field_moves_the_commitment`
    #[inline]
    #[must_use]
    pub const fn new(
        gear_table: GearTableVersion,
        seed_policy: SeedPolicy,
        normalization: NormalizationPolicy,
        record_boundary_rule: RecordBoundaryRule,
        limits: ChunkLimits,
    ) -> Self
    {
        Self {
            gear_table,
            seed_policy,
            normalization,
            record_boundary_rule,
            limits,
        }
    }

    /// Returns the default record-safe profile: the version-1 table, no salt,
    /// bytes preserved, cuts between records, and the default limits.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn default_fastcdc() -> Self
    {
        Self::new(
            GearTableVersion::V1,
            SeedPolicy::Unsalted,
            NormalizationPolicy::PreserveBytes,
            RecordBoundaryRule::BetweenRecords,
            ChunkLimits::default_fastcdc(),
        )
    }

    /// Returns the bytes a downstream root commits this profile as.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`crate::PARAMETER_DOMAIN`], the
    ///   [`AlgorithmVersion::FastCdc2020`] discriminator, then the fields in
    ///   the order this module's documentation lays out, every integer
    ///   little-endian at its fixed width.
    /// - provides: the opaque bytes a root binds, so two writers that disagree
    ///   on any field produce different roots rather than silently different
    ///   cuts.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 against independent full-image goldens, with L3 field
    ///   perturbations, distinguishes domain, tag, order, width and byte-order
    ///   mutations over validated profiles.
    /// - witness: `tests::commitment::the_default_record_safe_commitment_is_pinned`
    /// - witness: `tests::commitment::each_record_safe_field_moves_the_commitment`
    #[anodized::spec(ensures: |ret| ret.as_ref().strip_prefix(crate::PARAMETER_DOMAIN)
        .is_some_and(|fields| {
            fields.len() == 75
                && fields.get(0..2) == Some([1, 0].as_slice())
                && fields.get(2..4) == Some([1, 0].as_slice())
                && fields.get(4).copied().map(u16::from) == Some(u16::from(self.seed_policy.discriminator()))
                && fields.get(5..37) == Some(self.seed_policy.salt().as_ref())
                && fields.get(37..39) == Some([0, 0].as_slice())
                && fields.get(39..47) == Some(u64::from(self.limits.min_bytes).to_le_bytes().as_slice())
                && fields.get(47..55) == Some(u64::from(self.limits.target_bytes).to_le_bytes().as_slice())
                && fields.get(55..63) == Some(u64::from(self.limits.max_bytes).to_le_bytes().as_slice())
                && fields.get(63..67) == Some(u32::from(self.limits.min_records).to_le_bytes().as_slice())
                && fields.get(67..71) == Some(u32::from(self.limits.target_records).to_le_bytes().as_slice())
                && fields.get(71..75) == Some(u32::from(self.limits.max_records).to_le_bytes().as_slice())
        }))]
    #[inline]
    #[must_use]
    pub fn commitment(&self) -> ParameterCommitment
    {
        let salt = self.seed_policy.salt();
        let limits = self.limits;
        let mut writer = CommitmentWriter::open(AlgorithmVersion::FastCdc2020);

        writer.push(CommitmentField::Word(u16::from(
            self.gear_table.discriminator(),
        )));
        writer.push(self.seed_policy.discriminator().byte_field());
        writer.push(CommitmentField::Bytes(salt.as_ref()));
        writer.push(self.normalization.discriminator().byte_field());
        writer.push(self.record_boundary_rule.discriminator().byte_field());
        writer.push(CommitmentField::Long(u64::from(limits.min_bytes)));
        writer.push(CommitmentField::Long(u64::from(limits.target_bytes)));
        writer.push(CommitmentField::Long(u64::from(limits.max_bytes)));
        writer.push(CommitmentField::Int(u32::from(limits.min_records)));
        writer.push(CommitmentField::Int(u32::from(limits.target_records)));
        writer.push(CommitmentField::Int(u32::from(limits.max_records)));

        writer.finish()
    }

    /// Returns the Gear table version.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn gear_table(&self) -> GearTableVersion
    {
        self.gear_table
    }

    /// Returns the seed policy.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn seed_policy(&self) -> SeedPolicy
    {
        self.seed_policy
    }

    /// Returns the normalization policy.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn normalization(&self) -> NormalizationPolicy
    {
        self.normalization
    }

    /// Returns the record-boundary rule.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn record_boundary_rule(&self) -> RecordBoundaryRule
    {
        self.record_boundary_rule
    }

    /// Returns the validated limits.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn limits(&self) -> ChunkLimits
    {
        self.limits
    }

    /// Derives every chunk's initial Gear state from the seed policy.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the fixed initial state xored with the seed kind, then each
    ///   salt byte folded in by a five-bit rotation, an xor and a
    ///   multiplication, in salt order.
    /// - provides: the per-chunk starting state, a function of the committed
    ///   seed policy alone.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on unsalted, zero-salted and ascending-byte salts;
    ///   exact independently calculated words distinguish seed-kind, order,
    ///   rotation and mixing mutations, not collisions over every salt.
    /// - witness: `gear::tests::seed_states_match_independent_goldens`
    #[anodized::spec(ensures: |ret| ret.0 == self.seed_policy.salt().as_ref().iter().fold(
        GEAR_STATE_IV ^ u64::from(u16::from(self.seed_policy.discriminator())),
        |state, byte| (state.rotate_left(5) ^ u64::from(*byte)).wrapping_mul(SEED_MIX_MULTIPLIER),
    ))]
    fn initial_state(&self) -> GearState
    {
        let mut state = GEAR_STATE_IV ^ u64::from(u16::from(self.seed_policy.discriminator()));

        for byte in self.seed_policy.salt().as_ref() {
            state = state.rotate_left(5_u32) ^ u64::from(*byte);
            state = state.wrapping_mul(SEED_MIX_MULTIPLIER);
        }

        GearState(state)
    }

    /// Derives the cut mask from the target byte limit.
    ///
    /// # Specification
    /// - requires: the target is at most `u32::MAX`, which the limits enforce.
    /// - ensures: zero for a target of one, and otherwise one less than the
    ///   smallest power of two at or above the target, so a state masked to
    ///   zero has probability about one over the target.
    /// - provides: the hash predicate's mask.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 at one, powers of two, adjacent values and the largest
    ///   admitted target; exact masks separate rounding and subtraction faults.
    /// - witness: `gear::tests::cut_masks_round_up_at_power_boundaries`
    #[anodized::spec(ensures: |ret| ret.0.checked_add(1).is_some_and(|power| {
        let target = u64::from(self.limits.target_bytes);
        power.is_power_of_two() && power >= target
            && (power == 1 || power.checked_div(2).is_some_and(|half| half < target))
    }))]
    fn cut_mask(&self) -> CutMask
    {
        let target = u64::from(self.limits.target_bytes);
        let power = target.checked_next_power_of_two().unwrap_or(u64::MAX);

        CutMask(power.saturating_sub(1_u64))
    }
}

impl Default for ChunkerParams
{
    /// Returns [`ChunkerParams::default_fastcdc`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self::default_fastcdc()
    }
}

impl RawDiscriminator
{
    /// Returns the discriminator as an eight-bit committed field.
    ///
    /// # Specification
    /// - requires: the discriminator belongs to an eight-bit field, which every
    ///   call site's enum guarantees.
    /// - ensures: a one-byte field carrying the low eight bits of the
    ///   discriminator.
    /// - provides: the field an eight-bit discriminator is committed as.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 over the complete admitted eight-bit domain; the exact
    ///   byte payload distinguishes narrowing and field-width mutations.
    /// - witness: `gear::tests::byte_fields_preserve_every_admitted_discriminator`
    #[anodized::spec(
        requires: u8::try_from(self.0).is_ok(),
        ensures: |ret| matches!(ret, CommitmentField::Byte(value) if u16::from(value) == self.0),
    )]
    fn byte_field(self) -> CommitmentField<'static>
    {
        let [low, _high] = self.0.to_le_bytes();

        CommitmentField::Byte(low)
    }
}

/// Borrowed canonical bytes, for [`chunk_spans`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CanonicalBytes<'bytes>(&'bytes [u8]);

impl<'bytes> From<&'bytes [u8]> for CanonicalBytes<'bytes>
{
    /// Reads a byte slice as canonical bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: &'bytes [u8]) -> Self
    {
        Self(bytes)
    }
}

impl AsRef<[u8]> for CanonicalBytes<'_>
{
    /// Borrows the bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        self.0
    }
}

/// Borrowed canonical records in their committed order, for
/// [`chunk_record_slices`].
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CanonicalRecords<'records>(&'records [&'records [u8]]);

impl<'records> From<&'records [&'records [u8]]> for CanonicalRecords<'records>
{
    /// Reads a slice of record slices as canonical records.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(records: &'records [&'records [u8]]) -> Self
    {
        Self(records)
    }
}

impl<'records> AsRef<[&'records [u8]]> for CanonicalRecords<'records>
{
    /// Borrows the records.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[&'records [u8]]
    {
        self.0
    }
}

/// One record's bytes, as the scanner consumes them.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct RecordBytes<'record>(&'record [u8]);

/// Cuts borrowed canonical records into record-safe chunks.
///
/// # Specification
/// - requires: `records` is already canonical; nothing is normalized.
/// - ensures: on success the chunks partition the records' concatenated bytes
///   and their positions in order, every chunk containing at least one record,
///   every chunk within the hard caps, every byte span ending on a record edge,
///   and an empty input giving no chunk.
/// - provides: the record-safe scan over records the caller holds as slices,
///   copying no payload.
/// - fails: [`ChunkerError::RecordByteLengthCapViolation`] when one record
///   alone exceeds the byte cap; [`ChunkerError::ChunkByteCapViolation`] when a
///   record would carry an open chunk past the byte cap before the chunk met
///   its minimum limits; [`ChunkerError::ArithmeticOverflow`] when a position
///   exceeds its width.
/// - panics: none.
/// - intension: one pass, each byte read once, no lookahead past the record
///   being consumed.
///
/// # Errors
/// [`ChunkerError::RecordByteLengthCapViolation`] — a record exceeds the byte
/// cap.
/// [`ChunkerError::ChunkByteCapViolation`] — the byte cap conflicts with the
/// minimum limits.
/// [`ChunkerError::ArithmeticOverflow`] — a position exceeds its width.
///
/// # Adequacy
/// - hypothesis: L1 partition and cap relations against the input records, plus
///   L3 for cut causes, minimum suppression, empty records and named refusals,
///   observed through exact spans and error payloads. Agreement between entry
///   points checks representations, not an independent scanner. The one-pass
///   intension has no cost projection and is not witnessed here.
/// - witness: `tests::gear::identical_records_and_params_emit_identical_chunks`
/// - witness: `tests::gear::the_two_entry_points_agree`
/// - witness: `tests::gear::empty_input_and_final_remainder_partition_the_input`
/// - witness: `tests::gear::minimum_limits_suppress_an_early_hash_cut`
/// - witness: `tests::gear::the_caps_force_their_reasons`
/// - witness: `tests::gear::an_oversized_record_is_refused_by_name`
/// - witness: `tests::gear::an_unreachable_minimum_is_refused_by_name`
/// - witness: `tests::gear::low_entropy_streams_stay_within_the_caps`
/// - witness: `tests::gear::empty_records_keep_their_record_positions`
#[anodized::spec(ensures: |ret| ret.as_ref().map_or(true, |chunks| {
        let mut byte_end = BytePosition::ZERO;
        let mut record_end = RecordPosition::ZERO;
        let partition = chunks.iter().all(|chunk| {
            let bytes = chunk.bytes();
            let indices = chunk.records();
            let ordered = bytes.start() == byte_end && indices.start() == record_end
                && bytes.end() >= bytes.start() && indices.end() > indices.start();
            byte_end = bytes.end();
            record_end = indices.end();
            let (Ok(start), Ok(end)) = (usize::try_from(u64::from(indices.start())), usize::try_from(u64::from(indices.end()))) else { return false; };
            let Some(input) = records.as_ref().get(start..end) else { return false; };
            let input_len = input.iter().try_fold(0_u64, |sum, record| sum.checked_add(u64::try_from(record.len()).ok()?));
            ordered && u64::from(bytes.end()).checked_sub(u64::from(bytes.start())) == input_len
                && input_len.is_some_and(|len| len <= u64::from(params.limits.max_bytes))
                && u64::from(indices.end()).checked_sub(u64::from(indices.start())).is_some_and(|len| len <= u64::from(u32::from(params.limits.max_records)))
        });
        partition && usize::try_from(u64::from(record_end)).ok() == Some(records.as_ref().len())
}))]
#[inline]
pub fn chunk_record_slices(
    records: CanonicalRecords<'_>,
    params: &ChunkerParams,
) -> Result<Vec<ChunkSpan>, ChunkerError>
{
    let records = records.as_ref();
    let mut scan = ChunkScan::new(params, ScanCapacity(records.len()));
    let mut record_index = RecordPosition::ZERO;
    let mut next_start = BytePosition::ZERO;

    for record in records {
        let Ok(length) = u64::try_from(record.len())
        else {
            return Err(ChunkerError::ArithmeticOverflow {
                operation: ArithmeticOperation::RecordLength,
            });
        };
        let record_end =
            next_start.checked_advance(ByteCount::from(length), ArithmeticOperation::ByteOffset)?;
        scan.consume_record(record_index, next_start, record_end, RecordBytes(record))?;
        next_start = record_end;
        record_index = record_index.checked_next()?;
    }

    scan.finish()?;

    Ok(scan.chunks)
}

/// Cuts canonical bytes into record-safe chunks along caller-stated record
/// edges.
///
/// # Specification
/// - requires: `record_spans` is the caller's statement of where its records
///   lie; a statement that is not a partition is refused rather than trusted.
/// - ensures: on success exactly the chunks [`chunk_record_slices`] returns for
///   the records the spans delimit.
/// - provides: the record-safe scan over one contiguous buffer, borrowing each
///   record out of it.
/// - fails: [`ChunkerError::NonMonotonicRecordSpans`] when a span does not
///   start where the previous one ended or ends before it starts;
///   [`ChunkerError::RecordSpanOutOfBounds`] when a span ends past the bytes;
///   [`ChunkerError::UncoveredCanonicalBytes`] when the spans end before the
///   bytes do; and every refusal [`chunk_record_slices`] makes.
/// - panics: none.
///
/// # Errors
/// [`ChunkerError::NonMonotonicRecordSpans`] — the spans are not contiguous and
/// increasing.
/// [`ChunkerError::RecordSpanOutOfBounds`] — a span ends past the bytes.
/// [`ChunkerError::UncoveredCanonicalBytes`] — the spans stop short.
/// [`ChunkerError::RecordByteLengthCapViolation`],
/// [`ChunkerError::ChunkByteCapViolation`],
/// [`ChunkerError::ArithmeticOverflow`] — as [`chunk_record_slices`].
///
/// # Adequacy
/// - hypothesis: L1 partition relations and L3 at gap, overlap, inversion,
///   out-of-bounds, uncovered and equal-edge inputs; exact spans and named
///   refusals distinguish geometry mutations. Shared-entry agreement alone is
///   not an independent scanner oracle.
/// - witness: `tests::gear::the_two_entry_points_agree`
/// - witness: `tests::gear::span_lists_that_are_not_a_partition_are_refused`
/// - witness: `tests::gear::empty_records_keep_their_record_positions`
#[anodized::spec(ensures: |ret| ret.as_ref().map_or(true, |chunks| {
        let mut byte_end = BytePosition::ZERO;
        let mut record_end = RecordPosition::ZERO;
        let partition = chunks.iter().all(|chunk| {
            let bytes = chunk.bytes();
            let indices = chunk.records();
            let ordered = bytes.start() == byte_end && indices.start() == record_end
                && bytes.end() >= bytes.start() && indices.end() > indices.start();
            byte_end = bytes.end();
            record_end = indices.end();
            let (Ok(start), Ok(end)) = (usize::try_from(u64::from(indices.start())), usize::try_from(u64::from(indices.end()))) else { return false; };
            let Some(input) = record_spans.get(start..end) else { return false; };
            ordered && input.first().is_some_and(|span| span.start() == bytes.start())
                && input.last().is_some_and(|span| span.end() == bytes.end())
                && u64::from(bytes.end()).checked_sub(u64::from(bytes.start())).is_some_and(|len| len <= u64::from(params.limits.max_bytes))
                && u64::try_from(input.len()).is_ok_and(|len| len <= u64::from(u32::from(params.limits.max_records)))
        });
        partition && usize::try_from(u64::from(record_end)).ok() == Some(record_spans.len())
            && usize::try_from(u64::from(byte_end)).ok() == Some(canonical_bytes.as_ref().len())
}))]
#[inline]
pub fn chunk_spans(
    canonical_bytes: CanonicalBytes<'_>,
    record_spans: &[ByteSpan],
    params: &ChunkerParams,
) -> Result<Vec<ChunkSpan>, ChunkerError>
{
    let bytes = canonical_bytes.as_ref();
    let Ok(length) = u64::try_from(bytes.len())
    else {
        return Err(ChunkerError::ArithmeticOverflow {
            operation: ArithmeticOperation::ByteOffset,
        });
    };
    let canonical_len = BytePosition::from(length);
    let mut scan = ChunkScan::new(params, ScanCapacity(record_spans.len()));
    let mut expected_start = BytePosition::ZERO;
    let mut record_index = RecordPosition::ZERO;

    for span in record_spans {
        if span.start() != expected_start || span.end() < span.start() {
            return Err(ChunkerError::NonMonotonicRecordSpans {
                index: record_index,
            });
        }
        let out_of_bounds = ChunkerError::RecordSpanOutOfBounds {
            index: record_index,
            end: span.end(),
            canonical_len,
        };
        if span.end() > canonical_len {
            return Err(out_of_bounds);
        }
        let (Ok(start), Ok(end)) = (
            usize::try_from(u64::from(span.start())),
            usize::try_from(u64::from(span.end())),
        )
        else {
            return Err(ChunkerError::ArithmeticOverflow {
                operation: ArithmeticOperation::ByteOffset,
            });
        };
        let Some(record) = bytes.get(start .. end)
        else {
            return Err(out_of_bounds);
        };

        scan.consume_record(record_index, span.start(), span.end(), RecordBytes(record))?;
        expected_start = span.end();
        record_index = record_index.checked_next()?;
    }

    if expected_start != canonical_len {
        return Err(ChunkerError::UncoveredCanonicalBytes {
            covered_end: expected_start,
            canonical_len,
        });
    }

    scan.finish()?;

    Ok(scan.chunks)
}

/// How many boundaries a scan reserves room for: at most one per record.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ScanCapacity(usize);

/// Whether the open chunk has met both minimum limits.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum MinimumLimits
{
    /// Both minimums are met.
    Met,
    /// At least one minimum is not met.
    Unmet,
}

/// The mutable state of one record-safe scan.
///
/// # Specification
/// - requires: transitions are driven in record order with validated limits.
/// - ensures: successful transitions retain a bounded pending chunk and an
///   ordered prefix of completed record-aligned chunks.
/// - provides: one shared state machine for both input representations.
/// - fails: transition methods return the scan's named refusals.
/// - panics: none.
/// - executable: none — the invariant spans a transition sequence; individual
///   transitions and the final partition have executable postconditions.
///
/// # Adequacy
/// - hypothesis: L1 partitions against input records and L3 cap and remainder
///   boundaries; output geometry and reasons separate duplicate, missing and
///   misaligned transitions, without claiming every possible scan is covered.
/// - witness: `tests::gear::the_caps_force_their_reasons`
/// - witness: `tests::gear::empty_input_and_final_remainder_partition_the_input`
/// - witness: `tests::gear::low_entropy_streams_stay_within_the_caps`
struct ChunkScan
{
    /// The validated limits.
    limits: ChunkLimits,
    /// The state each chunk opens with.
    initial_state: GearState,
    /// The hash predicate's mask.
    cut_mask: CutMask,
    /// The chunks emitted so far.
    chunks: Vec<ChunkSpan>,
    /// The open chunk's Gear state.
    state: GearState,
    /// The open chunk's first byte.
    chunk_start_byte: BytePosition,
    /// The open chunk's first record.
    chunk_start_record: RecordPosition,
    /// The open chunk's byte count.
    chunk_bytes: ByteCount,
    /// The open chunk's record count.
    chunk_records: RecordCount,
    /// The end of the last consumed record.
    last_record_end: BytePosition,
}

impl ChunkScan
{
    /// Opens a scan with room for one boundary per record.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: no chunk emitted, the open chunk empty at position zero, and
    ///   its state the profile's initial state.
    /// - provides: the scan both entry points drive.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 at empty and below-minimum inputs; exact empty output
    ///   and final spans distinguish nonzero initialization and phantom chunks.
    /// - witness: `tests::gear::empty_input_and_final_remainder_partition_the_input`
    #[anodized::spec(ensures: |ret| ret.chunks.is_empty()
        && ret.chunk_start_byte == BytePosition::ZERO && ret.chunk_start_record == RecordPosition::ZERO
        && ret.chunk_bytes == ByteCount::ZERO && ret.chunk_records == RecordCount::ZERO
        && ret.last_record_end == BytePosition::ZERO && ret.state == params.initial_state()
        && ret.initial_state == ret.state && ret.limits == params.limits() && ret.cut_mask == params.cut_mask())]
    fn new(
        params: &ChunkerParams,
        capacity: ScanCapacity,
    ) -> Self
    {
        let initial_state = params.initial_state();

        Self {
            limits: params.limits(),
            initial_state,
            cut_mask: params.cut_mask(),
            chunks: Vec::with_capacity(capacity.0),
            state: initial_state,
            chunk_start_byte: BytePosition::ZERO,
            chunk_start_record: RecordPosition::ZERO,
            chunk_bytes: ByteCount::ZERO,
            chunk_records: RecordCount::ZERO,
            last_record_end: BytePosition::ZERO,
        }
    }

    /// Consumes one complete record and cuts after it when the rule says so.
    ///
    /// # Specification
    /// - requires: records arrive in order, each starting where the previous
    ///   one ended.
    /// - ensures: on success the record joins the open chunk — after first
    ///   closing it when the record would cross a cap the chunk may be cut at —
    ///   and the chunk is cut after the record when it reached a cap or met its
    ///   minimums with the masked state at zero.
    /// - provides: the scan's one step.
    /// - fails: as [`chunk_record_slices`] states for a single record.
    /// - panics: none.
    ///
    /// # Errors
    /// The cap and arithmetic refusals [`chunk_record_slices`] lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 at hash and cap cuts, minimum conflicts and oversized
    ///   records; exact spans, reasons and payloads separate cut precedence,
    ///   suppression and rejection mutations on these boundary corpora.
    /// - witness: `tests::gear::minimum_limits_suppress_an_early_hash_cut`
    /// - witness: `tests::gear::the_caps_force_their_reasons`
    /// - witness: `tests::gear::an_oversized_record_is_refused_by_name`
    /// - witness: `tests::gear::an_unreachable_minimum_is_refused_by_name`
    #[anodized::spec(
        requires: record_start == self.last_record_end,
        ensures: |ret| ret.is_err() || (self.last_record_end == record_end
            && self.chunk_bytes <= self.limits.max_bytes && self.chunk_records <= self.limits.max_records),
    )]
    fn consume_record(
        &mut self,
        record_index: RecordPosition,
        record_start: BytePosition,
        record_end: BytePosition,
        record: RecordBytes<'_>,
    ) -> Result<(), ChunkerError>
    {
        let record_len =
            record_end.checked_distance_from(record_start, ArithmeticOperation::RecordLength)?;
        let max_bytes = self.limits.max_bytes();
        let max_records = self.limits.max_records();

        if record_len > max_bytes {
            return Err(ChunkerError::RecordByteLengthCapViolation {
                record_index,
                record_len,
                max_bytes,
            });
        }

        // A record that would push a non-empty chunk past the byte cap closes
        // the chunk first, unless the chunk has not met its minimums — then no
        // legal cut exists and the limits are refused for this input. The
        // record cap needs no such check: a chunk is closed the moment it
        // reaches that cap, below.
        if self.chunk_records != RecordCount::ZERO {
            let bytes_if_added = self
                .chunk_bytes
                .checked_plus(record_len, ArithmeticOperation::ChunkByteCount)?;

            if bytes_if_added > max_bytes {
                if self.minimum_limits() == MinimumLimits::Unmet {
                    return Err(ChunkerError::ChunkByteCapViolation {
                        chunk_start_record: self.chunk_start_record,
                        next_record_index: record_index,
                        attempted_bytes: bytes_if_added,
                        max_bytes,
                    });
                }
                self.emit(BoundaryReason::MaxByteCap)?;
            }
        }

        if self.chunk_records == RecordCount::ZERO {
            self.chunk_start_byte = record_start;
            self.chunk_start_record = record_index;
            self.state = self.initial_state;
        }

        for byte in record.0 {
            let gear = GEAR_TABLE_V1
                .0
                .get(usize::from(*byte))
                .copied()
                .unwrap_or(0_u64);
            self.state = GearState(self.state.0.rotate_left(1_u32).wrapping_add(gear));
        }
        self.chunk_bytes = self
            .chunk_bytes
            .checked_plus(record_len, ArithmeticOperation::ChunkByteCount)?;
        self.chunk_records = self
            .chunk_records
            .checked_increment(ArithmeticOperation::ChunkRecordCount)?;
        self.last_record_end = record_end;

        if self.chunk_bytes == max_bytes {
            self.emit(BoundaryReason::MaxByteCap)?;
        }
        else if self.chunk_records == max_records {
            self.emit(BoundaryReason::MaxRecordCap)?;
        }
        else if self.minimum_limits() == MinimumLimits::Met
            && (self.state.0 & self.cut_mask.0) == 0_u64
        {
            self.emit(BoundaryReason::HashPredicate)?;
        }

        Ok(())
    }

    /// Emits the open chunk, if any, as the final remainder.
    ///
    /// # Specification
    /// - requires: every record has been consumed.
    /// - ensures: a non-empty open chunk is emitted with
    ///   [`BoundaryReason::FinalRemainder`]; an empty one emits nothing.
    /// - provides: the scan's last step.
    /// - fails: [`ChunkerError::ArithmeticOverflow`] when the chunk's end
    ///   position exceeds its width.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ChunkerError::ArithmeticOverflow`] — a position exceeds its width.
    ///
    /// # Adequacy
    /// - hypothesis: L3 at empty and nonempty remainder states, and the record
    ///   position width; exact final spans and overflow identity distinguish
    ///   omission, phantom emission, wrong reasons and arithmetic wrapping.
    /// - witness: `tests::gear::empty_input_and_final_remainder_partition_the_input`
    /// - witness: `gear::tests::record_position_overflow_refuses_without_emission`
    #[anodized::spec(
        captures: before = (self.chunks.len(), self.chunk_records),
        ensures: |ret| ret.is_err() || (self.chunk_records == RecordCount::ZERO
            && self.chunk_bytes == ByteCount::ZERO
            && if before.1 == RecordCount::ZERO { self.chunks.len() == before.0 }
            else { self.chunks.len() == before.0.saturating_add(1)
                && self.chunks.last().is_some_and(|chunk| chunk.reason() == BoundaryReason::FinalRemainder) }),
    )]
    fn finish(&mut self) -> Result<(), ChunkerError>
    {
        self.emit(BoundaryReason::FinalRemainder)
    }

    /// Reports whether the open chunk has met both minimum limits.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`MinimumLimits::Met`] exactly when the chunk's bytes and
    ///   records are both at or above their minimums.
    /// - provides: the gate on the hash predicate and on cap conflicts.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on the cross-product of each minimum's lower neighbor,
    ///   equality and upper neighbor; the decision separates conjunction,
    ///   field-swap and strict-comparison mutations.
    /// - witness: `gear::tests::minimum_limits_require_both_thresholds`
    #[anodized::spec(ensures: |ret| (ret == MinimumLimits::Met)
        == (self.chunk_bytes >= self.limits.min_bytes && self.chunk_records >= self.limits.min_records))]
    fn minimum_limits(&self) -> MinimumLimits
    {
        if self.chunk_bytes >= self.limits.min_bytes()
            && self.chunk_records >= self.limits.min_records()
        {
            MinimumLimits::Met
        }
        else {
            MinimumLimits::Unmet
        }
    }

    /// Emits the open chunk and opens an empty one after it.
    ///
    /// # Specification
    /// - requires: nothing; an empty open chunk emits nothing.
    /// - ensures: a non-empty open chunk is pushed with `reason`, its byte span
    ///   ending at the last consumed record and its record span covering its
    ///   records; the next chunk opens empty there with the initial state.
    /// - provides: the one place a chunk is emitted.
    /// - fails: [`ChunkerError::ArithmeticOverflow`] when the chunk's end
    ///   position exceeds its width.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ChunkerError::ArithmeticOverflow`] — a position exceeds its width.
    ///
    /// # Adequacy
    /// - hypothesis: L1 output partition relations and L3 at all cut reasons,
    ///   empty input and record-position overflow; spans, reasons and refusal
    ///   identity separate omission, duplicate output, wrong edges and
    ///   wrapping.
    /// - witness: `tests::gear::the_caps_force_their_reasons`
    /// - witness: `tests::gear::empty_input_and_final_remainder_partition_the_input`
    /// - witness: `tests::gear::minimum_limits_suppress_an_early_hash_cut`
    /// - witness: `gear::tests::record_position_overflow_refuses_without_emission`
    #[anodized::spec(
        captures: before = (self.chunks.len(), self.chunk_records, self.chunk_start_byte, self.last_record_end, self.chunk_start_record),
        ensures: |ret| {
            if before.1 == RecordCount::ZERO { ret.is_ok() && self.chunks.len() == before.0 }
            else {
                match (ret, before.4.checked_advance(before.1)) {
                    (Ok(()), Ok(end)) => self.chunks.len() == before.0.saturating_add(1)
                        && self.chunks.last().is_some_and(|chunk| *chunk == ChunkSpan::new(
                            ByteSpan::new(before.2, before.3), RecordSpan::new(before.4, end), reason))
                        && self.chunk_start_byte == before.3 && self.chunk_start_record == end
                        && self.chunk_bytes == ByteCount::ZERO && self.chunk_records == RecordCount::ZERO
                        && self.state == self.initial_state,
                    (Err(actual), Err(expected)) => actual == expected && self.chunks.len() == before.0,
                    _ => false,
                }
            }
        },
    )]
    fn emit(
        &mut self,
        reason: BoundaryReason,
    ) -> Result<(), ChunkerError>
    {
        if self.chunk_records == RecordCount::ZERO {
            return Ok(());
        }

        let record_end = self
            .chunk_start_record
            .checked_advance(self.chunk_records)?;
        self.chunks.push(ChunkSpan::new(
            ByteSpan::new(self.chunk_start_byte, self.last_record_end),
            RecordSpan::new(self.chunk_start_record, record_end),
            reason,
        ));
        self.chunk_start_byte = self.last_record_end;
        self.chunk_start_record = record_end;
        self.chunk_bytes = ByteCount::ZERO;
        self.chunk_records = RecordCount::ZERO;
        self.state = self.initial_state;

        Ok(())
    }
}

#[cfg(test)]
mod tests
{
    use super::GEAR_TABLE_V1;

    #[test]
    fn the_v1_table_is_pinned()
    {
        // The first two, a middle and the last entry of the table as first
        // published: a seed, increment or mixing constant that moved would
        // move all of them.
        assert_eq!(GEAR_TABLE_V1.0.first(), Some(&0x63CF_C62A_2B09_7592_u64));
        assert_eq!(GEAR_TABLE_V1.0.get(1), Some(&0xDC07_46B4_1946_6AEC_u64));
        assert_eq!(GEAR_TABLE_V1.0.get(0x80), Some(&0x9F92_CAD8_40DB_5CD4_u64));
        assert_eq!(GEAR_TABLE_V1.0.last(), Some(&0xCED3_4DD0_5B9A_775A_u64));
    }

    #[test]
    fn seed_states_match_independent_goldens()
    {
        let ascending =
            core::array::from_fn(|index| u8::try_from(index).expect("32-byte salt index fits"));
        for (seed_policy, expected) in [
            (super::SeedPolicy::Unsalted, 0x5A45_4035_DEB9_6AFE),
            (
                super::SeedPolicy::PublicSalt(super::SeedSalt::from([0; 32])),
                0x85C6_E179_78E7_AA3B,
            ),
            (
                super::SeedPolicy::PublicSalt(super::SeedSalt::from(ascending)),
                0x4BB7_BA7F_FB32_B3B0,
            ),
        ] {
            let params = super::ChunkerParams {
                seed_policy,
                ..super::ChunkerParams::default_fastcdc()
            };
            assert_eq!(params.initial_state(), super::GearState(expected));
        }
    }

    #[test]
    fn cut_masks_round_up_at_power_boundaries()
    {
        for (target, expected) in [
            (1, 0),
            (2, 1),
            (3, 3),
            (4, 3),
            (5, 7),
            (0x7FFF_FFFF, 0x7FFF_FFFF),
            (0x8000_0000, 0x7FFF_FFFF),
            (0x8000_0001, 0xFFFF_FFFF),
            (u64::from(u32::MAX), 0xFFFF_FFFF),
        ] {
            let limits = super::ChunkLimits::new(
                1_u64.into(),
                target.into(),
                target.into(),
                1_u32.into(),
                1_u32.into(),
                1_u32.into(),
            )
            .expect("ordered positive limits");
            let params = super::ChunkerParams {
                limits,
                ..super::ChunkerParams::default_fastcdc()
            };
            assert_eq!(
                params.cut_mask(),
                super::CutMask(expected),
                "target {target}"
            );
        }
    }

    #[test]
    fn byte_fields_preserve_every_admitted_discriminator()
    {
        for raw in 0_u8 ..= u8::MAX {
            assert!(matches!(super::RawDiscriminator::from(raw).byte_field(),
                super::CommitmentField::Byte(value) if value == raw));
        }
    }

    #[test]
    fn minimum_limits_require_both_thresholds()
    {
        let limits = super::ChunkLimits::new(
            4_u64.into(),
            8_u64.into(),
            16_u64.into(),
            2_u32.into(),
            4_u32.into(),
            8_u32.into(),
        )
        .expect("ordered positive limits");
        let params = super::ChunkerParams {
            limits,
            ..super::ChunkerParams::default_fastcdc()
        };
        let mut scan = super::ChunkScan::new(&params, super::ScanCapacity(0));
        for (bytes, bytes_met) in [(3_u64, false), (4, true), (5, true)] {
            for (records, records_met) in [(1_u32, false), (2, true), (3, true)] {
                scan.chunk_bytes = bytes.into();
                scan.chunk_records = records.into();
                let expected = if bytes_met && records_met {
                    super::MinimumLimits::Met
                }
                else {
                    super::MinimumLimits::Unmet
                };
                assert_eq!(
                    scan.minimum_limits(),
                    expected,
                    "bytes {bytes}, records {records}"
                );
            }
        }
    }

    #[test]
    fn record_position_overflow_refuses_without_emission()
    {
        let mut scan = super::ChunkScan::new(
            &super::ChunkerParams::default_fastcdc(),
            super::ScanCapacity(1),
        );
        scan.chunk_start_record = super::RecordPosition::from(u64::MAX);
        scan.chunk_records = super::RecordCount::from(1_u32);
        scan.chunk_bytes = super::ByteCount::from(1_u64);
        scan.last_record_end = super::BytePosition::from(1_u64);
        assert_eq!(
            scan.finish(),
            Err(super::ChunkerError::ArithmeticOverflow {
                operation: super::ArithmeticOperation::RecordIndex,
            })
        );
        assert!(scan.chunks.is_empty());
        assert_eq!(scan.chunk_records, super::RecordCount::from(1_u32));
        let start = u64::MAX.checked_sub(1).expect("positive width");
        scan.chunk_start_record = super::RecordPosition::from(start);
        assert_eq!(scan.finish(), Ok(()));
        let expected = super::ChunkSpan::new(
            super::ByteSpan::new(super::BytePosition::ZERO, super::BytePosition::from(1_u64)),
            super::RecordSpan::new(
                super::RecordPosition::from(start),
                super::RecordPosition::from(u64::MAX),
            ),
            super::BoundaryReason::FinalRemainder,
        );
        assert_eq!(scan.chunks.as_slice(), [expected].as_slice());
        assert_eq!(scan.finish(), Ok(()));
        assert_eq!(scan.chunks.as_slice(), [expected].as_slice());
    }
}
