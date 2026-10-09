//! The committed parameter block: the domain it opens with, the algorithm
//! discriminator, and the byte image a downstream root binds.
//!
//! # Why the parameters are committed
//!
//! Where a cut falls is protocol material. Two writers that disagree on kappa,
//! the cap, the Gear table or a byte limit cut the same input differently,
//! produce different chunks, and share nothing — with no error anywhere,
//! because inside each writer everything is consistent. A downstream root that
//! binds these bytes turns that silent disagreement into a refusal.
//!
//! # The layout
//!
//! ```text
//! commitment := PARAMETER_DOMAIN || u16le algorithm || profile fields
//! ```
//!
//! The domain names the byte language and its version, so a commitment cannot
//! be read as any other material a downstream hash binds beside it; the
//! algorithm discriminator selects which profile's fields follow. Every
//! integer is little-endian at a fixed width. Each profile documents its own
//! fields where it is defined.

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::fmt;

use crate::error::ChunkerError;
use crate::error::ProfileField;
use crate::error::RawDiscriminator;

/// The domain every parameter commitment opens with.
pub const PARAMETER_DOMAIN: &[u8] = b"gandr:storage-chunker:params:v1";

/// The algorithm a committed profile cuts by.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each variant has one fixed discriminator, distinct across the
///   enum and never derived from the variant's position.
/// - provides: the selector a commitment opens with after its domain, so a
///   reader that does not implement a profile refuses its commitment instead of
///   misreading the fields that follow.
/// - fails: never.
/// - panics: none.
/// - executable: none — discriminator uniqueness relates all enum variants; the
///   conversion predicate checks the executable wire-value mapping.
///
/// # Adequacy
/// - hypothesis: L3 only — the discriminator table is a finite class,
///   enumerated with both admitted values and the first refused value on each
///   side asserted exactly.
/// - witness: `tests::commitment::raw_discriminators_round_trip_and_refuse_by_field`
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum AlgorithmVersion
{
    /// The record-safe Gear scanner over canonical record bytes, after the
    /// `FastCDC` family.
    FastCdc2020,
    /// The typed scanner over caller-reported boundary events.
    TypedCdc,
}

impl AlgorithmVersion
{
    /// Returns the discriminator this algorithm is committed under.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `1` for [`AlgorithmVersion::FastCdc2020`] and `2` for
    ///   [`AlgorithmVersion::TypedCdc`].
    /// - provides: the value [`TryFrom<u16>`] reads back.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 exhausts every raw sixteen-bit value, observing the
    ///   exact variant or field-and-value refusal; L2 profile goldens fix
    ///   discriminator bytes. Renumbering and variant swaps are distinguished.
    /// - witness: `tests::commitment::raw_discriminators_round_trip_and_refuse_by_field`
    /// - witness: `tests::commitment::the_typed_commitment_is_pinned`
    /// - witness: `tests::commitment::the_default_record_safe_commitment_is_pinned`
    #[anodized::spec(ensures: |ret| ret.0 == match self { Self::FastCdc2020 => 1_u16, Self::TypedCdc => 2_u16 })]
    #[inline]
    #[must_use]
    pub const fn discriminator(self) -> RawDiscriminator
    {
        match self {
            | Self::FastCdc2020 => RawDiscriminator(0x0001_u16),
            | Self::TypedCdc => RawDiscriminator(0x0002_u16),
        }
    }
}

impl TryFrom<u16> for AlgorithmVersion
{
    type Error = ChunkerError;

    /// Reads a raw algorithm discriminator, refusing one this build does not
    /// implement.
    ///
    /// # Specification
    /// - requires: nothing; the value is arbitrary.
    /// - ensures: on success the variant whose discriminator is `raw`.
    /// - provides: the only way from a raw value to an algorithm.
    /// - fails: [`ChunkerError::UnsupportedProfileValue`] naming the algorithm
    ///   field and `raw` for any other value.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ChunkerError::UnsupportedProfileValue`] — `raw` names no algorithm.
    ///
    /// # Adequacy
    /// - hypothesis: L3 exhausts all sixteen-bit inputs, including zero, both
    ///   admitted discriminators, their successor and the maximum; exact
    ///   variants and refusal payloads distinguish changed guards and mappings.
    /// - witness: `tests::commitment::raw_discriminators_round_trip_and_refuse_by_field`
    #[anodized::spec(ensures: |ret| ret == match raw {
        1 => Ok(Self::FastCdc2020),
        2 => Ok(Self::TypedCdc),
        _ => Err(ChunkerError::UnsupportedProfileValue {
            field: ProfileField::Algorithm, raw: RawDiscriminator(raw),
        }),
    })]
    #[inline]
    fn try_from(raw: u16) -> Result<Self, Self::Error>
    {
        [Self::FastCdc2020, Self::TypedCdc]
            .into_iter()
            .find(|algorithm| u16::from(algorithm.discriminator()) == raw)
            .ok_or(ChunkerError::UnsupportedProfileValue {
                field: ProfileField::Algorithm,
                raw: RawDiscriminator(raw),
            })
    }
}

/// The committed bytes of a chunking profile, opaque to everything that
/// carries them.
///
/// A downstream root binds these bytes rather than the parsed parameters, so a
/// reader that does not implement a profile refuses a root built under it
/// instead of misreading one.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ParameterCommitment(Box<[u8]>);

impl AsRef<[u8]> for ParameterCommitment
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

impl fmt::Display for ParameterCommitment
{
    /// Writes the committed bytes as lowercase hexadecimal.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes two lowercase hexadecimal digits per byte, in byte
    ///   order, and nothing else.
    /// - provides: a rendering a refusal or a log line can carry.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L2 hexadecimal goldens for empty bytes and bytes spanning
    ///   zero, the nibble boundary and 255 distinguish padding, case, ordering
    ///   and omission faults; L3 observes a refusing sink's exact fmt error.
    /// - witness: `commitment::tests::hexadecimal_rendering_preserves_bytes_and_sink_failure`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        for byte in self.0.as_ref() {
            write!(f, "{byte:02x}")?;
        }

        Ok(())
    }
}

/// One fixed-width field of a commitment, as the writer appends it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum CommitmentField<'bytes>
{
    /// One byte.
    Byte(u8),
    /// A little-endian sixteen-bit field.
    Word(u16),
    /// A little-endian thirty-two-bit field.
    Int(u32),
    /// A little-endian sixty-four-bit field.
    Long(u64),
    /// Raw bytes with no framing of their own.
    Bytes(&'bytes [u8]),
}

/// An append-only writer for one commitment image.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct CommitmentWriter(Vec<u8>);

impl CommitmentWriter
{
    /// Opens a commitment for `algorithm`: the domain, then its discriminator.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the writer holds exactly [`PARAMETER_DOMAIN`] followed by the
    ///   algorithm's discriminator as a little-endian sixteen-bit field.
    /// - provides: the header every profile's commitment shares.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 observes complete commitment byte images for both
    ///   algorithms and mixed-width fields; changed domain bytes, version,
    ///   endian order and an extra or missing header byte disagree with
    ///   goldens.
    /// - witness: `tests::commitment::the_typed_commitment_is_pinned`
    /// - witness: `tests::commitment::the_default_record_safe_commitment_is_pinned`
    /// - witness: `commitment::tests::field_encoding_preserves_order_and_all_widths`
    #[anodized::spec(ensures: |ret| ret.0.len() == PARAMETER_DOMAIN.len().saturating_add(2)
        && ret.0.starts_with(PARAMETER_DOMAIN)
        && ret.0.ends_with(&algorithm.discriminator().0.to_le_bytes()))]
    pub(crate) fn open(algorithm: AlgorithmVersion) -> Self
    {
        let mut writer = Self(Vec::new());
        writer.push(CommitmentField::Bytes(PARAMETER_DOMAIN));
        writer.push(CommitmentField::Word(u16::from(algorithm.discriminator())));

        writer
    }

    /// Appends one field.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: appends the field's bytes, integers least-significant byte
    ///   first, and changes nothing already appended.
    /// - provides: the one place a commitment chooses a byte order.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 observes the entire encoded image after appending all
    ///   field widths, including empty and non-empty raw bytes. Mixed non-zero
    ///   bytes distinguish truncation, endian swaps, prefix damage and
    ///   reordering.
    /// - witness: `commitment::tests::field_encoding_preserves_order_and_all_widths`
    #[anodized::spec(
        captures: before = self.0.len(),
        ensures: match field {
            CommitmentField::Byte(value) => self.0.get(before..) == Some([value].as_slice()),
            CommitmentField::Word(value) => self.0.get(before..) == Some(value.to_le_bytes().as_slice()),
            CommitmentField::Int(value) => self.0.get(before..) == Some(value.to_le_bytes().as_slice()),
            CommitmentField::Long(value) => self.0.get(before..) == Some(value.to_le_bytes().as_slice()),
            CommitmentField::Bytes(bytes) => self.0.get(before..) == Some(bytes),
        },
    )]
    pub(crate) fn push(
        &mut self,
        field: CommitmentField<'_>,
    )
    {
        match field {
            | CommitmentField::Byte(byte) => self.0.push(byte),
            | CommitmentField::Word(word) => {
                self.0.extend_from_slice(word.to_le_bytes().as_slice());
            },
            | CommitmentField::Int(int) => self.0.extend_from_slice(int.to_le_bytes().as_slice()),
            | CommitmentField::Long(long) => {
                self.0.extend_from_slice(long.to_le_bytes().as_slice());
            },
            | CommitmentField::Bytes(bytes) => self.0.extend_from_slice(bytes),
        }
    }

    /// Closes the writer into the committed bytes.
    ///
    /// # Specification
    /// trivial.
    pub(crate) fn finish(self) -> ParameterCommitment
    {
        ParameterCommitment(self.0.into_boxed_slice())
    }
}

#[cfg(test)]
mod tests
{
    use alloc::format;
    use alloc::vec;
    use core::fmt;
    use core::fmt::Write as _;

    use super::AlgorithmVersion;
    use super::CommitmentField;
    use super::CommitmentWriter;
    use super::ParameterCommitment;

    #[test]
    fn field_encoding_preserves_order_and_all_widths()
    {
        let mut writer = CommitmentWriter::open(AlgorithmVersion::TypedCdc);
        writer.push(CommitmentField::Byte(0xAB));
        writer.push(CommitmentField::Word(0x1234));
        writer.push(CommitmentField::Int(0x1234_5678));
        writer.push(CommitmentField::Long(0x0123_4567_89AB_CDEF));
        writer.push(CommitmentField::Bytes(&[]));
        writer.push(CommitmentField::Bytes(&[0, 255]));
        let mut expected = b"gandr:storage-chunker:params:v1".to_vec();
        expected.extend_from_slice(&[
            2, 0, 0xAB, 0x34, 0x12, 0x78, 0x56, 0x34, 0x12, 0xEF, 0xCD, 0xAB, 0x89, 0x67, 0x45,
            0x23, 0x01, 0, 255,
        ]);
        assert_eq!(writer.finish().as_ref(), expected);
    }

    #[test]
    fn hexadecimal_rendering_preserves_bytes_and_sink_failure()
    {
        let empty = ParameterCommitment(vec![].into_boxed_slice());
        assert_eq!(format!("{empty}"), "");
        let image = ParameterCommitment(vec![0, 1, 15, 16, 171, 255].into_boxed_slice());
        assert_eq!(format!("{image}"), "00010f10abff");
        assert_eq!(write!(RefusingSink, "{image}"), Err(fmt::Error));
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
        /// - witness: `commitment::tests::hexadecimal_rendering_preserves_bytes_and_sink_failure`
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
