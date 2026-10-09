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
    /// - executable: none — the formatter's output sink cannot be read back.
    ///
    /// # Adequacy
    /// - hypothesis: L3 exhausts all eight parameter-refusal reasons, observing
    ///   pairwise-distinct renderings and the exact error from a refusing sink.
    ///   Collapsed alternatives and swallowed sink failures differ under these
    ///   observations; wording remains unconstrained.
    /// - witness: `error::tests::refusal_classes_remain_distinguishable`
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
    /// - executable: none — the formatter's output sink cannot be read back.
    ///
    /// # Adequacy
    /// - hypothesis: L3 exhausts all five arithmetic-operation variants,
    ///   observing pairwise-distinct renderings and the exact error from a
    ///   refusing sink. Collapsed alternatives and swallowed sink failures
    ///   differ under these observations; wording remains unconstrained.
    /// - witness: `error::tests::refusal_classes_remain_distinguishable`
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
    /// - executable: none — the formatter's output sink cannot be read back.
    ///
    /// # Adequacy
    /// - hypothesis: L3 exhausts all four profile-field variants, observing
    ///   pairwise-distinct renderings and the exact error from a refusing sink.
    ///   Collapsed alternatives and swallowed sink failures differ under these
    ///   observations; wording remains unconstrained.
    /// - witness: `error::tests::refusal_classes_remain_distinguishable`
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
    /// - executable: none — the formatter's output sink cannot be read back.
    ///
    /// # Adequacy
    /// - hypothesis: L2 compares decimal rendering with the primitive at zero,
    ///   37 and `u16::MAX`, including zero padding; L3 observes the exact
    ///   refusal of a failing sink. Substituted values, lost formatting options
    ///   and swallowed failures are distinguishable.
    /// - witness: `error::tests::refusal_rendering_retains_each_payload`
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
    /// - executable: none — the formatter's output sink cannot be read back.
    ///
    /// # Adequacy
    /// - hypothesis: L3 enumerates every refusal class and varies numeric
    ///   payloads over zero, an ordinary value and the maximum; rendered
    ///   distinctions and payload text detect collapsed variants and lost
    ///   values. A refusing sink distinguishes swallowed formatter failures.
    /// - witness: `error::tests::refusal_rendering_retains_each_payload`
    /// - witness: `error::tests::refusal_classes_remain_distinguishable`
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

#[cfg(test)]
mod tests
{
    use alloc::format;
    use alloc::string::String;
    use core::fmt;
    use core::fmt::Write as _;

    use super::ArithmeticOperation;
    use super::ChunkerError;
    use super::InvalidParameterReason;
    use super::ProfileField;
    use super::RawDiscriminator;
    use crate::units::ByteCount;
    use crate::units::BytePosition;
    use crate::units::RecordPosition;

    #[test]
    fn refusal_classes_remain_distinguishable()
    {
        let distinct = |images: &[String]| {
            for (index, image) in images.iter().enumerate() {
                for other in images.iter().skip(index.saturating_add(1)) {
                    assert_ne!(image, other);
                }
            }
        };
        let reasons = [
            InvalidParameterReason::ZeroByteLimit,
            InvalidParameterReason::MinByteExceedsTargetByte,
            InvalidParameterReason::InvertedByteLimits,
            InvalidParameterReason::TargetByteExceedsU32,
            InvalidParameterReason::ZeroRecordLimit,
            InvalidParameterReason::InvertedRecordLimits,
            InvalidParameterReason::ZeroKappa,
            InvalidParameterReason::ZeroTokenCap,
        ];
        distinct(&reasons.map(|value| format!("{value}")));
        for value in reasons {
            assert!(
                format!("{}", ChunkerError::InvalidParameters { reason: value })
                    .contains(&format!("{value}"))
            );
            assert_eq!(write!(RefusingSink, "{value}"), Err(fmt::Error));
        }
        let operations = [
            ArithmeticOperation::ByteOffset,
            ArithmeticOperation::RecordIndex,
            ArithmeticOperation::RecordLength,
            ArithmeticOperation::ChunkByteCount,
            ArithmeticOperation::ChunkRecordCount,
        ];
        distinct(&operations.map(|value| format!("{value}")));
        for value in operations {
            assert!(
                format!("{}", ChunkerError::ArithmeticOverflow { operation: value })
                    .contains(&format!("{value}"))
            );
            assert_eq!(write!(RefusingSink, "{value}"), Err(fmt::Error));
        }
        let fields = [
            ProfileField::Algorithm,
            ProfileField::GearTable,
            ProfileField::Normalization,
            ProfileField::RecordBoundaryRule,
        ];
        distinct(&fields.map(|value| format!("{value}")));
        for value in fields {
            assert!(
                format!("{}", ChunkerError::UnsupportedProfileValue {
                    field: value,
                    raw: RawDiscriminator(37)
                })
                .contains(&format!("{value}"))
            );
            assert_eq!(write!(RefusingSink, "{value}"), Err(fmt::Error));
        }
        let errors = [
            ChunkerError::InvalidParameters {
                reason: InvalidParameterReason::ZeroKappa,
            },
            ChunkerError::ArithmeticOverflow {
                operation: ArithmeticOperation::ByteOffset,
            },
            ChunkerError::UnsupportedProfileValue {
                field: ProfileField::Algorithm,
                raw: RawDiscriminator(17),
            },
            ChunkerError::NonMonotonicRecordSpans {
                index: RecordPosition::from(19_u64),
            },
            ChunkerError::RecordSpanOutOfBounds {
                index: RecordPosition::from(19_u64),
                end: BytePosition::from(23_u64),
                canonical_len: BytePosition::from(29_u64),
            },
            ChunkerError::UncoveredCanonicalBytes {
                covered_end: BytePosition::from(23_u64),
                canonical_len: BytePosition::from(29_u64),
            },
            ChunkerError::RecordByteLengthCapViolation {
                record_index: RecordPosition::from(19_u64),
                record_len: ByteCount::from(23_u64),
                max_bytes: ByteCount::from(29_u64),
            },
            ChunkerError::ChunkByteCapViolation {
                chunk_start_record: RecordPosition::from(17_u64),
                next_record_index: RecordPosition::from(19_u64),
                attempted_bytes: ByteCount::from(23_u64),
                max_bytes: ByteCount::from(29_u64),
            },
        ];
        distinct(&errors.map(|value| format!("{value}")));
        for value in errors {
            assert_eq!(write!(RefusingSink, "{value}"), Err(fmt::Error));
        }
    }

    #[test]
    fn refusal_rendering_retains_each_payload()
    {
        for raw in [0_u64, 37, u64::MAX] {
            let position = RecordPosition::from(raw);
            let bytes = BytePosition::from(raw);
            let count = ByteCount::from(raw);
            let needle = format!("{raw}");
            for error in [
                ChunkerError::NonMonotonicRecordSpans { index: position },
                ChunkerError::RecordSpanOutOfBounds {
                    index: position,
                    end: BytePosition::ZERO,
                    canonical_len: BytePosition::ZERO,
                },
                ChunkerError::RecordSpanOutOfBounds {
                    index: RecordPosition::ZERO,
                    end: bytes,
                    canonical_len: BytePosition::ZERO,
                },
                ChunkerError::RecordSpanOutOfBounds {
                    index: RecordPosition::ZERO,
                    end: BytePosition::ZERO,
                    canonical_len: bytes,
                },
                ChunkerError::UncoveredCanonicalBytes {
                    covered_end: bytes,
                    canonical_len: BytePosition::ZERO,
                },
                ChunkerError::UncoveredCanonicalBytes {
                    covered_end: BytePosition::ZERO,
                    canonical_len: bytes,
                },
                ChunkerError::RecordByteLengthCapViolation {
                    record_index: position,
                    record_len: ByteCount::ZERO,
                    max_bytes: ByteCount::ZERO,
                },
                ChunkerError::RecordByteLengthCapViolation {
                    record_index: RecordPosition::ZERO,
                    record_len: count,
                    max_bytes: ByteCount::ZERO,
                },
                ChunkerError::RecordByteLengthCapViolation {
                    record_index: RecordPosition::ZERO,
                    record_len: ByteCount::ZERO,
                    max_bytes: count,
                },
                ChunkerError::ChunkByteCapViolation {
                    chunk_start_record: position,
                    next_record_index: RecordPosition::ZERO,
                    attempted_bytes: ByteCount::ZERO,
                    max_bytes: ByteCount::ZERO,
                },
                ChunkerError::ChunkByteCapViolation {
                    chunk_start_record: RecordPosition::ZERO,
                    next_record_index: position,
                    attempted_bytes: ByteCount::ZERO,
                    max_bytes: ByteCount::ZERO,
                },
                ChunkerError::ChunkByteCapViolation {
                    chunk_start_record: RecordPosition::ZERO,
                    next_record_index: RecordPosition::ZERO,
                    attempted_bytes: count,
                    max_bytes: ByteCount::ZERO,
                },
                ChunkerError::ChunkByteCapViolation {
                    chunk_start_record: RecordPosition::ZERO,
                    next_record_index: RecordPosition::ZERO,
                    attempted_bytes: ByteCount::ZERO,
                    max_bytes: count,
                },
            ] {
                assert!(format!("{error}").contains(&needle));
            }
        }
        for raw in [0_u16, 37, u16::MAX] {
            let error = ChunkerError::UnsupportedProfileValue {
                field: ProfileField::GearTable,
                raw: RawDiscriminator(raw),
            };
            assert!(format!("{error}").contains(&format!("{raw}")));
            assert_eq!(format!("{:08}", RawDiscriminator(raw)), format!("{raw:08}"));
        }
        assert_eq!(
            write!(RefusingSink, "{}", RawDiscriminator(37)),
            Err(fmt::Error)
        );
    }

    /// A sink that refuses every write.
    struct RefusingSink;

    impl fmt::Write for RefusingSink
    {
        /// Refuses a write.
        ///
        /// # Specification
        /// - requires: nothing; the offered text is arbitrary.
        /// - ensures: every write returns the formatter's error.
        /// - provides: a sink that exercises formatter refusal propagation.
        /// - fails: always returns `fmt::Error`.
        /// - panics: none.
        ///
        /// # Adequacy
        /// - hypothesis: L3 on text emitted by this module's formatter cases;
        ///   the exact formatting result distinguishes falsely accepted writes.
        /// - witness: `error::tests::refusal_classes_remain_distinguishable`
        #[anodized::spec(ensures: |ret| ret == Err(fmt::Error))]
        fn write_str(
            &mut self,
            _text: &str,
        ) -> fmt::Result
        {
            Err(fmt::Error)
        }
    }
}
