//! The byte plane: the artifact image types and the scalar wrappers every
//! encode and decode step passes through.
//!
//! Nothing here knows a term from a level. The module exists so that the
//! format's integer and byte positions carry their meaning in their type: a
//! tag byte, a decoded count, and a byte offset are three different things that
//! are all one machine word, and a signature that spelled them `u8`/`usize`
//! would let any two of them be swapped without a compiler error.
//!
//! The unsigned LEB128 primitive lives here too, in both directions, because
//! the writer's minimality and the reader's overlong rejection are one
//! commitment stated twice: a value has exactly one byte image, which is what
//! makes the canonical-form comparison in [`decode`] meaningful.
//!
//! [`decode`]: mod@crate::decode

use alloc::vec::Vec;

use anodized::spec;

/// One byte read from or written to the artifact image.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct WireByte(pub u8);

impl From<u8> for WireByte
{
    /// The wire byte for a raw byte.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(byte: u8) -> Self
    {
        Self(byte)
    }
}

impl From<WireByte> for u8
{
    /// The raw byte the wrapper carries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(byte: WireByte) -> Self
    {
        byte.0
    }
}

/// One tag byte: the discriminating byte at a tagged position of the format.
///
/// Every tagged position — the node tags, the declaration kinds, the admission
/// marks, the base-type atoms, the literal kinds, the signs, the injection
/// sides, and the constraint relations — draws from this one type, and the
/// position is named separately by [`TagSite`]. The alphabets are disjoint per
/// position rather than globally, so the pair of a tag and its site is what
/// identifies a byte, and that pair is exactly what a refusal reports.
///
/// [`TagSite`]: crate::TagSite
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct WireTag(pub u8);

impl From<u8> for WireTag
{
    /// The tag for a raw byte.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(tag: u8) -> Self
    {
        Self(tag)
    }
}

impl From<WireTag> for u8
{
    /// The raw byte the tag carries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(tag: WireTag) -> Self
    {
        tag.0
    }
}

impl From<WireByte> for WireTag
{
    /// The byte read at a tagged position, as a tag.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(byte: WireByte) -> Self
    {
        Self(byte.0)
    }
}

impl From<WireTag> for WireByte
{
    /// The tag as the byte written for it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(tag: WireTag) -> Self
    {
        Self(tag.0)
    }
}

impl core::fmt::Display for WireTag
{
    /// Writes the tag as a two-digit hexadecimal byte.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes `0x` followed by exactly two lowercase hexadecimal
    ///   digits.
    /// - provides: the spelling an unknown-tag refusal carries, so the message
    ///   names the byte as the format writes it rather than as a decimal
    ///   number.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        write!(f, "0x{:02x}", self.0)
    }
}

/// The declared format version of an artifact.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FormatVersion(pub u16);

impl From<u16> for FormatVersion
{
    /// The version for a raw number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(version: u16) -> Self
    {
        Self(version)
    }
}

impl From<FormatVersion> for u16
{
    /// The raw number the version carries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(version: FormatVersion) -> Self
    {
        version.0
    }
}

impl core::fmt::Display for FormatVersion
{
    /// Writes the version as a decimal number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        self.0.fmt(f)
    }
}

/// A decoded or encoded 32-bit wire integer.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct WireU32(pub u32);

impl From<u32> for WireU32
{
    /// The wire integer for a raw number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: u32) -> Self
    {
        Self(value)
    }
}

impl From<WireU32> for u32
{
    /// The raw number the wire integer carries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: WireU32) -> Self
    {
        value.0
    }
}

/// A decoded or encoded 64-bit wire integer.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct WireU64(pub u64);

impl From<u64> for WireU64
{
    /// The wire integer for a raw number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: u64) -> Self
    {
        Self(value)
    }
}

impl From<WireU64> for u64
{
    /// The raw number the wire integer carries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: WireU64) -> Self
    {
        value.0
    }
}

/// A decoded or encoded host-sized wire count.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct WireUsize(pub usize);

impl From<usize> for WireUsize
{
    /// The wire count for a raw count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: usize) -> Self
    {
        Self(value)
    }
}

impl From<WireUsize> for usize
{
    /// The raw count the wire count carries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: WireUsize) -> Self
    {
        value.0
    }
}

impl From<WireUsize> for WireU64
{
    /// Widen a host count to the wire's 64-bit integer.
    ///
    /// `usize` is at most 64 bits on every supported platform, so the widening
    /// is lossless there; the saturating fallback keeps the conversion total on
    /// a hypothetical wider platform rather than introducing a failure mode no
    /// caller could act on.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: returns the equal 64-bit integer, or the `u64` ceiling on a
    ///   platform whose pointer is wider than 64 bits.
    /// - provides: the total, panic-free widening from a host count to the
    ///   wire's integer; the saturation is a documented ceiling rather than a
    ///   reachable path on any supported platform.
    /// - panics: none.
    #[inline]
    fn from(value: WireUsize) -> Self
    {
        Self(u64::try_from(value.0).unwrap_or(u64::MAX))
    }
}

/// An offset into an artifact image, and the length of one.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ByteOffset(pub usize);

impl From<usize> for ByteOffset
{
    /// The offset for a raw position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(offset: usize) -> Self
    {
        Self(offset)
    }
}

impl From<ByteOffset> for usize
{
    /// The raw position the offset carries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(offset: ByteOffset) -> Self
    {
        offset.0
    }
}

/// A count of bytes requested from an artifact image.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ByteCount(pub usize);

impl From<usize> for ByteCount
{
    /// The count for a raw number of bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: usize) -> Self
    {
        Self(count)
    }
}

impl From<ByteCount> for usize
{
    /// The raw number of bytes the count carries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: ByteCount) -> Self
    {
        count.0
    }
}

/// Borrowed UTF-8 text offered to the wire encoder.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ArtifactText<'text>(pub &'text str);

impl<'text> From<&'text str> for ArtifactText<'text>
{
    /// The wire text for borrowed UTF-8.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: &'text str) -> Self
    {
        Self(text)
    }
}

impl AsRef<str> for ArtifactText<'_>
{
    /// Borrow the text.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &str
    {
        self.0
    }
}

/// Borrowed canonical artifact bytes offered to the validating decoder.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ArtifactImage<'artifact>(&'artifact [u8]);

impl<'artifact> From<&'artifact [u8]> for ArtifactImage<'artifact>
{
    /// The image for borrowed bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: &'artifact [u8]) -> Self
    {
        Self(bytes)
    }
}

impl AsRef<[u8]> for ArtifactImage<'_>
{
    /// Borrow the image's bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        self.0
    }
}

impl ArtifactImage<'_>
{
    /// The number of bytes in this image.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) fn length(self) -> ByteOffset
    {
        ByteOffset(self.0.len())
    }

    /// The sub-image over `range`, or `None` when the range leaves the image.
    ///
    /// # Specification
    /// - requires: nothing — an inverted or out-of-range span is admissible
    ///   input, since the bytes may be adversarial.
    /// - ensures: `Some(image)` over exactly the requested half-open span when
    ///   it lies inside this image, `None` otherwise.
    /// - provides: the bounds-checked slice the byte cursor reads through, so
    ///   no read is ever an index.
    /// - fails: returns `None` on any span the image does not contain.
    /// - panics: none.
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.is_some() == (range.start.0 <= range.end.0 && range.end.0 <= self.0.len()))]
    pub(crate) fn span(
        self,
        range: core::ops::Range<ByteOffset>,
    ) -> Option<Self>
    {
        self.0.get(range.start.0 .. range.end.0).map(Self)
    }

    /// The byte at `offset`, or `None` past the end.
    ///
    /// # Specification
    /// - requires: nothing — an out-of-range offset is admissible input, since
    ///   the bytes may be adversarial.
    /// - ensures: returns the byte at `offset` when it lies inside this image,
    ///   and `None` otherwise.
    /// - provides: the bounds-checked single-byte read the cursor advances
    ///   through, so no read is ever an index.
    /// - panics: none.
    #[inline]
    #[must_use]
    pub(crate) fn byte_at(
        self,
        offset: ByteOffset,
    ) -> Option<WireByte>
    {
        self.0.get(offset.0).copied().map(WireByte)
    }
}

/// An owned canonical artifact byte image.
///
/// It is the encoder's only output type and the unit the canonical-form
/// comparison is stated over: an artifact is canonical exactly when re-encoding
/// what it decoded reproduces the same [`EncodedArtifact`].
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct EncodedArtifact(Vec<u8>);

impl AsRef<[u8]> for EncodedArtifact
{
    /// Borrow the image's bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        self.0.as_slice()
    }
}

impl From<EncodedArtifact> for Vec<u8>
{
    /// The bytes the image owns.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(artifact: EncodedArtifact) -> Self
    {
        artifact.0
    }
}

impl EncodedArtifact
{
    /// An empty image.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub(crate) fn new() -> Self
    {
        Self(Vec::new())
    }

    /// Borrow these bytes for decoding or comparison.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn as_image(&self) -> ArtifactImage<'_>
    {
        ArtifactImage(self.0.as_slice())
    }

    /// Append one tag byte.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn put_tag(
        &mut self,
        tag: WireTag,
    )
    {
        self.0.push(tag.0);
    }

    /// Append the bytes of `image` verbatim.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn put_image(
        &mut self,
        image: ArtifactImage<'_>,
    )
    {
        self.0.extend_from_slice(image.0);
    }

    /// Append a format version as two little-endian bytes.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: appends exactly two bytes, the version's little-endian image.
    /// - provides: the header's version framing, fixed at two bytes so the
    ///   field's width does not depend on the value written.
    /// - panics: none.
    #[inline]
    pub(crate) fn put_version(
        &mut self,
        version: FormatVersion,
    )
    {
        self.0.extend_from_slice(&version.0.to_le_bytes());
    }

    /// Append the minimal unsigned LEB128 encoding of `value`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: appends the little-endian base-128 encoding with no
    ///   continuation byte past the highest set group, so a given value has
    ///   exactly one byte image.
    /// - provides: the encoder's integer primitive, matched by [`decode`]'s
    ///   overlong-rejecting reader.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the round-trip differential over the encoder and the
    ///   decoder pins minimality on every artifact; the L3 residues are the
    ///   single-byte value, the exact group boundary at 128, and the `u64`
    ///   ceiling, asserted as exact byte images.
    /// - witness: `wire::tests::uvarint_images_are_minimal_at_the_boundaries`
    /// - witness: `wire::tests::uvarint_round_trips_through_the_reader`
    ///
    /// [`decode`]: mod@crate::decode
    // The predicate covers the terminator half of minimality: at least one byte
    // is appended, and the last one clears the continuation bit. The
    // no-redundant-group half is the reader's overlong rejection, which is where
    // the round-trip differential states it.
    #[spec(captures: [entry_len = self.0.len()], ensures: self.0.len() > entry_len && self.0.last().is_some_and(|&byte| byte < 0x80))]
    pub(crate) fn put_uvarint(
        &mut self,
        value: WireU64,
    )
    {
        let mut remaining = value.0;
        loop {
            let low = u8::try_from(remaining & 0x7f).unwrap_or(0_u8);
            remaining = remaining.wrapping_shr(7);
            if remaining == 0_u64 {
                self.0.push(low);
                return;
            }
            self.0.push(low | 0x80);
        }
    }
}

#[cfg(test)]
mod tests
{
    use alloc::vec;
    use alloc::vec::Vec;

    use super::EncodedArtifact;
    use super::WireU64;
    use crate::decode::ByteReader;

    #[test]
    fn uvarint_images_are_minimal_at_the_boundaries()
    {
        let image_of = |value: u64| {
            let mut out = EncodedArtifact::new();
            out.put_uvarint(WireU64::from(value));
            Vec::from(out)
        };
        assert_eq!(vec![0x00_u8], image_of(0));
        assert_eq!(vec![0x7f_u8], image_of(127));
        assert_eq!(vec![0x80_u8, 0x01], image_of(128));
        assert_eq!(
            vec![
                0xff_u8, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x01
            ],
            image_of(u64::MAX)
        );
    }

    #[test]
    fn uvarint_round_trips_through_the_reader()
    {
        for value in [0_u64, 1, 127, 128, 300, 0x3fff, 0x4000, u64::MAX] {
            let mut out = EncodedArtifact::new();
            out.put_uvarint(WireU64::from(value));
            let mut reader = ByteReader::new(out.as_image());
            let read = reader.read_uvarint().expect("a written varint reads back");
            assert_eq!(value, u64::from(read), "varint {value} round-trips");
        }
    }
}
