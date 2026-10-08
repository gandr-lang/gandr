//! The crate's single typed failure vocabulary, [`ChunkerError`].

use core::error::Error;
use core::fmt;

use crate::units::ByteCount;
use crate::units::BytePosition;
use crate::units::RecordPosition;

/// Why a set of chunk limits or typed constants was refused.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum InvalidParameterReason
{
    /// A byte limit was zero.
    ZeroByteLimit,
    /// The minimum byte limit exceeded the target.
    MinByteExceedsTargetByte,
    /// The target byte limit exceeded the maximum.
    InvertedByteLimits,
    /// The target byte limit exceeded the widest target the Gear mask is
    /// derived for.
    TargetByteExceedsU32,
    /// A record limit was zero.
    ZeroRecordLimit,
    /// The record limits were not ordered minimum, target, maximum.
    InvertedRecordLimits,
    /// The typed profile's kappa was zero.
    ZeroKappa,
    /// The typed profile's token cap was zero.
    ZeroTokenCap,
}

impl fmt::Display for InvalidParameterReason
{
    /// Writes the refused condition.
    ///
    /// # Specification
    /// - requires: nothing; every variant renders.
    /// - ensures: writes one fixed phrase per variant, no two alike.
    /// - provides: the condition a parameter refusal names.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::ZeroByteLimit => "a byte limit is zero",
            | Self::MinByteExceedsTargetByte => "the minimum byte limit exceeds the target",
            | Self::InvertedByteLimits => "the target byte limit exceeds the maximum",
            | Self::TargetByteExceedsU32 => "the target byte limit exceeds u32::MAX",
            | Self::ZeroRecordLimit => "a record limit is zero",
            | Self::InvertedRecordLimits => {
                "the record limits are not ordered minimum, target, maximum"
            },
            | Self::ZeroKappa => "kappa is zero",
            | Self::ZeroTokenCap => "the token cap is zero",
        })
    }
}

/// The quantity whose checked arithmetic overflowed.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ArithmeticOperation
{
    /// A byte offset or a canonical byte-stream length.
    ByteOffset,
    /// A record index.
    RecordIndex,
    /// A record's byte length.
    RecordLength,
    /// A chunk's byte count.
    ChunkByteCount,
    /// A chunk's record count.
    ChunkRecordCount,
}

impl fmt::Display for ArithmeticOperation
{
    /// Writes the quantity that overflowed.
    ///
    /// # Specification
    /// - requires: nothing; every variant renders.
    /// - ensures: writes one fixed phrase per variant, no two alike.
    /// - provides: the quantity an overflow refusal names.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::ByteOffset => "byte offset",
            | Self::RecordIndex => "record index",
            | Self::RecordLength => "record length",
            | Self::ChunkByteCount => "chunk byte count",
            | Self::ChunkRecordCount => "chunk record count",
        })
    }
}

/// A committed profile field whose raw value names no variant this build
/// implements.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ProfileField
{
    /// The algorithm discriminator.
    Algorithm,
    /// The Gear table version.
    GearTable,
    /// The input normalization policy.
    Normalization,
    /// The record-boundary rule.
    RecordBoundaryRule,
}

impl fmt::Display for ProfileField
{
    /// Writes the field's name.
    ///
    /// # Specification
    /// - requires: nothing; every variant renders.
    /// - ensures: writes one fixed phrase per variant, no two alike.
    /// - provides: the field an unsupported-value refusal names.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            | Self::Algorithm => "algorithm",
            | Self::GearTable => "Gear table version",
            | Self::Normalization => "normalization policy",
            | Self::RecordBoundaryRule => "record-boundary rule",
        })
    }
}

/// A raw profile discriminator, as a caller or a commitment supplied it.
///
/// The value is whatever was offered, so it is reported rather than
/// interpreted: an unknown discriminator is a refusal, never a fallback.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RawDiscriminator(pub u16);

impl From<u16> for RawDiscriminator
{
    /// Reads a sixteen-bit discriminator.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(raw: u16) -> Self
    {
        Self(raw)
    }
}

impl From<u8> for RawDiscriminator
{
    /// Reads an eight-bit discriminator, widened exactly.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(raw: u8) -> Self
    {
        Self(u16::from(raw))
    }
}

impl From<RawDiscriminator> for u16
{
    /// Reads the discriminator back out.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(raw: RawDiscriminator) -> Self
    {
        raw.0
    }
}

impl fmt::Display for RawDiscriminator
{
    /// Writes the discriminator as a number.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the carried number through the `u16` rendering.
    /// - provides: the value an unsupported-value refusal names, uninterpreted.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        fmt::Display::fmt(&self.0, f)
    }
}

/// Every way this crate refuses an input.
///
/// Refusal is the crate's only failure mode: no operation panics and no
/// operation repairs an input it was handed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ChunkerError
{
    /// Limits or typed constants were zero or out of order.
    InvalidParameters
    {
        /// The refused condition.
        reason: InvalidParameterReason,
    },

    /// Checked arithmetic overflowed while deriving an offset or a count.
    ArithmeticOverflow
    {
        /// The quantity that overflowed.
        operation: ArithmeticOperation,
    },

    /// A profile field named a value this build does not implement.
    UnsupportedProfileValue
    {
        /// The field.
        field: ProfileField,
        /// The value offered for it.
        raw: RawDiscriminator,
    },

    /// Record byte spans were not a contiguous increasing partition.
    NonMonotonicRecordSpans
    {
        /// The position of the offending span.
        index: RecordPosition,
    },

    /// A record span ended past the canonical byte stream.
    RecordSpanOutOfBounds
    {
        /// The position of the offending span.
        index: RecordPosition,
        /// Where the span ended.
        end: BytePosition,
        /// The canonical byte stream's length.
        canonical_len: BytePosition,
    },

    /// The record spans ended before the canonical byte stream did.
    UncoveredCanonicalBytes
    {
        /// Where the last span ended.
        covered_end: BytePosition,
        /// The canonical byte stream's length.
        canonical_len: BytePosition,
    },

    /// One complete record exceeded the hard byte cap on its own.
    RecordByteLengthCapViolation
    {
        /// The record's position.
        record_index: RecordPosition,
        /// The record's length.
        record_len: ByteCount,
        /// The hard byte cap.
        max_bytes: ByteCount,
    },

    /// The next record would cross the byte cap before the chunk met its
    /// minimum limits.
    ChunkByteCapViolation
    {
        /// The first record of the chunk being built.
        chunk_start_record: RecordPosition,
        /// The record that would cross the cap.
        next_record_index: RecordPosition,
        /// The size the chunk would reach.
        attempted_bytes: ByteCount,
        /// The hard byte cap.
        max_bytes: ByteCount,
    },
}

impl fmt::Display for ChunkerError
{
    /// Writes the refusal and the values it names.
    ///
    /// # Specification
    /// - requires: nothing; every variant renders.
    /// - ensures: writes one message per variant, each naming the reason,
    ///   field, position, or count its payload carries, so no two variants
    ///   render alike.
    /// - provides: the operator-facing sentence a caller prints, and the
    ///   [`Error`] rendering the implementation below inherits.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            | Self::InvalidParameters { reason } => {
                write!(f, "chunker parameters are invalid: {reason}")
            },
            | Self::ArithmeticOverflow { operation } => {
                write!(f, "arithmetic overflowed computing a {operation}")
            },
            | Self::UnsupportedProfileValue { field, raw } => {
                write!(f, "unsupported {field} {raw}")
            },
            | Self::NonMonotonicRecordSpans { index } => {
                write!(f, "record span {index} does not continue the partition")
            },
            | Self::RecordSpanOutOfBounds {
                index,
                end,
                canonical_len,
            } => {
                write!(
                    f,
                    "record span {index} ends at {end}, past the canonical length {canonical_len}"
                )
            },
            | Self::UncoveredCanonicalBytes {
                covered_end,
                canonical_len,
            } => {
                write!(
                    f,
                    "record spans cover bytes to {covered_end}, not the canonical length {canonical_len}"
                )
            },
            | Self::RecordByteLengthCapViolation {
                record_index,
                record_len,
                max_bytes,
            } => {
                write!(
                    f,
                    "record {record_index} is {record_len} bytes, over the chunk cap of {max_bytes}"
                )
            },
            | Self::ChunkByteCapViolation {
                chunk_start_record,
                next_record_index,
                attempted_bytes,
                max_bytes,
            } => {
                write!(
                    f,
                    "the chunk from record {chunk_start_record} cannot take record {next_record_index}: {attempted_bytes} bytes exceed the cap of {max_bytes}"
                )
            },
        }
    }
}

impl Error for ChunkerError
{
}
