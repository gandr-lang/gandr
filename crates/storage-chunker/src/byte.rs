//! The byte profile: a Gear scan over one byte string that may cut after any
//! byte.
//!
//! # The rule
//!
//! Each chunk keeps a Gear state that starts at zero. Each byte mixes into
//! it: the state shifts left by one and adds the table's value for the byte.
//! A shift drops the state's top bit, so a byte leaves the state after 64
//! steps. After each byte the chunk ends when it reaches the maximum, or when
//! it holds at least the minimum and the state masked by the target's
//! power-of-two mask is zero. The minimum is at least 64 bytes, so the state
//! at a candidate cut holds only bytes of the chunk, and a cut depends on the
//! 64 bytes before it alone. An edit therefore moves only the cuts of the
//! chunk it falls in and of the chunk after it; every later cut stays in its
//! place.
//!
//! A salt mixes only into the state a chunk starts from, and a shifted state
//! forgets its start within 64 bytes, so the profile takes no seed policy.
//!
//! # The committed fields
//!
//! ```text
//! profile fields := u16le Gear table version
//!                || u64le min bytes || u64le target bytes || u64le max bytes
//! ```

use alloc::vec::Vec;

use anodized::spec;

use crate::commitment::AlgorithmVersion;
use crate::commitment::CommitmentField;
use crate::commitment::CommitmentWriter;
use crate::commitment::ParameterCommitment;
use crate::error::ChunkerError;
use crate::error::InvalidParameterReason;
use crate::gear::CanonicalBytes;
use crate::gear::GearTableVersion;
use crate::span::ByteSpan;
use crate::units::ByteCount;

/// The fewest bytes a chunk of the byte profile holds before the hash may cut
/// it: the steps after which a shifted state holds none of its start.
pub const GEAR_WINDOW: u64 = 64_u64;

/// The byte limits of the byte profile.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ByteLimits
{
    /// Bytes a chunk must reach before the hash may cut it.
    min: ByteCount,
    /// Bytes the cut mask is derived from.
    target: ByteCount,
    /// Bytes no chunk may exceed.
    max: ByteCount,
}

impl ByteLimits
{
    /// Validates a set of byte limits.
    ///
    /// # Specification
    /// - requires: nothing; the limits are arbitrary.
    /// - ensures: on success the limits carry exactly the three values offered.
    /// - provides: validation of arbitrary inputs before a scan trusts them.
    /// - fails: [`ChunkerError::InvalidParameters`] with the first refused
    ///   condition, checked in this order: a zero limit, a minimum under
    ///   [`GEAR_WINDOW`], a minimum over the target, a target over the maximum,
    ///   and a target over `u32::MAX`.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ChunkerError::InvalidParameters`] — the reason names the refused
    /// condition.
    ///
    /// # Adequacy
    /// - hypothesis: L3 at each refused condition and its first admitted
    ///   neighbour, with the exact reason observed.
    /// - witness: `tests::byte::each_refused_limit_names_its_reason`
    #[spec(ensures: |ret| ret.as_ref().map_or(true, |limits| limits.min == min_bytes
        && limits.target == target_bytes && limits.max == max_bytes))]
    #[inline]
    pub fn new(
        min_bytes: ByteCount,
        target_bytes: ByteCount,
        max_bytes: ByteCount,
    ) -> Result<Self, ChunkerError>
    {
        let reason = if min_bytes == ByteCount::ZERO
            || target_bytes == ByteCount::ZERO
            || max_bytes == ByteCount::ZERO
        {
            InvalidParameterReason::ZeroByteLimit
        }
        else if u64::from(min_bytes) < GEAR_WINDOW {
            InvalidParameterReason::MinByteUnderGearWindow
        }
        else if min_bytes > target_bytes {
            InvalidParameterReason::MinByteExceedsTargetByte
        }
        else if target_bytes > max_bytes {
            InvalidParameterReason::InvertedByteLimits
        }
        else if u64::from(target_bytes) > u64::from(u32::MAX) {
            InvalidParameterReason::TargetByteExceedsU32
        }
        else {
            return Ok(Self {
                min: min_bytes,
                target: target_bytes,
                max: max_bytes,
            });
        };

        Err(ChunkerError::InvalidParameters { reason })
    }

    /// The limits of a blob: chunks of 4 KiB to 64 KiB around a 16 KiB target.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn blob() -> Self
    {
        Self {
            min: ByteCount::from(0x1000_u64),
            target: ByteCount::from(0x4000_u64),
            max: ByteCount::from(0x0001_0000_u64),
        }
    }

    /// The bytes a chunk must reach before the hash may cut it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn min_bytes(&self) -> ByteCount
    {
        self.min
    }

    /// The bytes the cut mask is derived from.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn target_bytes(&self) -> ByteCount
    {
        self.target
    }

    /// The bytes no chunk may exceed.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn max_bytes(&self) -> ByteCount
    {
        self.max
    }
}

/// The parameters of the byte profile.
///
/// # Specification
/// - requires: nothing beyond what [`ByteLimits::new`] enforces.
/// - ensures: two parameter sets are equal exactly when their commitments are
///   equal, because the commitment encodes every field and nothing else.
/// - provides: the rule a byte scan cuts by, in a form a downstream root can
///   bind.
/// - fails: never, once constructed.
/// - panics: none.
/// - executable: none — injectivity relates two parameter sets; the commitment
///   method checks each concrete image.
///
/// # Adequacy
/// - hypothesis: L2 on the blob profile's commitment, a golden written out
///   field by field, and L3 for each field moving the commitment.
/// - witness: `tests::byte::the_blob_commitment_is_pinned`
/// - witness: `tests::byte::each_field_moves_the_commitment`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ByteChunkerParams
{
    /// The Gear table bytes are mixed with.
    gear_table: GearTableVersion,
    /// The validated limits.
    limits: ByteLimits,
}

impl ByteChunkerParams
{
    /// A byte profile from a table and validated limits.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        gear_table: GearTableVersion,
        limits: ByteLimits,
    ) -> Self
    {
        Self { gear_table, limits }
    }

    /// The profile of a blob: the version-2 table and [`ByteLimits::blob`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn blob() -> Self
    {
        Self::new(GearTableVersion::V2, ByteLimits::blob())
    }

    /// The limits the profile cuts under.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn limits(&self) -> ByteLimits
    {
        self.limits
    }

    /// The bytes a downstream root commits this profile as.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`crate::PARAMETER_DOMAIN`], the
    ///   [`AlgorithmVersion::GearBytes`] discriminator, the table version and
    ///   the three limits, every integer little-endian at its fixed width.
    /// - provides: the bytes a blob's root binds, so two writers that cut under
    ///   different limits produce different roots.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 against the blob profile's full image, and L3 for each
    ///   field moving the image.
    /// - witness: `tests::byte::the_blob_commitment_is_pinned`
    /// - witness: `tests::byte::each_field_moves_the_commitment`
    #[spec(ensures: |ret| ret.as_ref().strip_prefix(crate::PARAMETER_DOMAIN)
        .is_some_and(|fields| fields.len() == 28
            && fields.get(0 .. 2) == Some(AlgorithmVersion::GearBytes.discriminator().0.to_le_bytes().as_slice())
            && fields.get(2 .. 4) == Some(self.gear_table.discriminator().0.to_le_bytes().as_slice())
            && fields.get(4 .. 12) == Some(u64::from(self.limits.min).to_le_bytes().as_slice())
            && fields.get(12 .. 20) == Some(u64::from(self.limits.target).to_le_bytes().as_slice())
            && fields.get(20 .. 28) == Some(u64::from(self.limits.max).to_le_bytes().as_slice())))]
    #[inline]
    #[must_use]
    pub fn commitment(&self) -> ParameterCommitment
    {
        let mut writer = CommitmentWriter::open(AlgorithmVersion::GearBytes);
        writer.push(CommitmentField::Word(u16::from(
            self.gear_table.discriminator(),
        )));
        writer.push(CommitmentField::Long(u64::from(self.limits.min)));
        writer.push(CommitmentField::Long(u64::from(self.limits.target)));
        writer.push(CommitmentField::Long(u64::from(self.limits.max)));

        writer.finish()
    }
}

/// Cuts one byte string into content-defined chunks under `params`.
///
/// # Specification
/// - requires: nothing; the bytes are arbitrary.
/// - ensures: on success the chunks partition the bytes in order, each nonempty
///   and at most the maximum, each but the last at least the minimum; a chunk
///   ends where the maximum stops it or, past the minimum, where the masked
///   state is zero. Empty bytes give no chunk.
/// - provides: the cut of a blob's bytes, which the store keeps one chunk at a
///   time.
/// - fails: [`ChunkerError::ArithmeticOverflow`] when a position exceeds its
///   width.
/// - panics: none.
/// - intension: one pass, each byte read once, no lookahead.
///
/// # Errors
/// [`ChunkerError::ArithmeticOverflow`] — a position exceeds its width.
///
/// # Adequacy
/// - hypothesis: L1 partition and size relations over generated bytes; L3 for a
///   byte put before a stream, which keeps every cut past the first chunk one
///   byte later, and for a stream of one byte value, which the maximum cuts.
/// - witness: `tests::byte::the_chunks_partition_the_bytes_within_the_limits`
/// - witness: `tests::byte::a_byte_put_before_a_stream_moves_no_later_cut`
/// - witness: `tests::byte::a_stream_of_one_byte_value_is_cut_at_the_maximum`
#[spec(ensures: |ret| ret.as_ref().map_or(true, |chunks| {
    let mut end = 0_u64;
    let ordered = chunks.iter().all(|chunk| {
        let start = u64::from(chunk.start());
        let stop = u64::from(chunk.end());
        let length = stop.saturating_sub(start);
        let ordered = start == end && stop > start && length <= u64::from(params.limits.max);
        end = stop;
        ordered
    });
    ordered && usize::try_from(end).ok() == Some(bytes.as_ref().len())
}))]
#[inline]
pub fn chunk_bytes(
    bytes: CanonicalBytes<'_>,
    params: &ByteChunkerParams,
) -> Result<Vec<ByteSpan>, ChunkerError>
{
    params.gear_table.cut_shifted(bytes, &params.limits)
}
