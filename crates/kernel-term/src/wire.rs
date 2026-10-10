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
///
/// # Specification
/// - requires: the payload is interpreted in the named wire coordinate or
///   framing role.
/// - ensures: retains raw bytes or the carried quantity without claiming that a
///   decoder will admit it; canonicality is established by complete encoding or
///   validated decoding.
/// - panics: none.
/// - executable: none — this wire carrier has no invocation boundary; byte
///   projection, framing and reader validation carry its executable
///   obligations.
///
/// # Adequacy
/// - hypothesis: L3 observes byte/range boundaries and complete mixed-field
///   images; L2 compares varint bytes with an independent arithmetic reference.
///   Nominal role separation is L0. The carrier alone does not prove
///   canonicality or node admission.
/// - witness: `wire::tests::image_ranges_and_bytes_match_independent_projections`
/// - witness: `wire::tests::wire_fields_preserve_prefixes_and_little_endian_order`
/// - witness: `wire::tests::varints_match_a_quotient_reference_at_every_group_boundary`
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
///
/// # Specification
/// - requires: the payload is interpreted in the named wire coordinate or
///   framing role.
/// - ensures: retains raw bytes or the carried quantity without claiming that a
///   decoder will admit it; canonicality is established by complete encoding or
///   validated decoding.
/// - panics: none.
/// - executable: none — this wire carrier has no invocation boundary; byte
///   projection, framing and reader validation carry its executable
///   obligations.
///
/// # Adequacy
/// - hypothesis: L3 observes byte/range boundaries and complete mixed-field
///   images; L2 compares varint bytes with an independent arithmetic reference.
///   Nominal role separation is L0. The carrier alone does not prove
///   canonicality or node admission.
/// - witness: `wire::tests::image_ranges_and_bytes_match_independent_projections`
/// - witness: `wire::tests::wire_fields_preserve_prefixes_and_little_endian_order`
/// - witness: `wire::tests::varints_match_a_quotient_reference_at_every_group_boundary`
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
    /// - executable: none — Formatter exposes no readable output or
    ///   sink-refusal state; checking either here would require wrapping or
    ///   replaying the write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 observes all byte-valued tag spellings, version
    ///   boundaries and a real exhausted byte sink. The assertions separate
    ///   radix, width, case, numeric truncation and swallowed refusal;
    ///   unrelated diagnostic prose is not pinned.
    /// - witness: `error::tests::diagnostics_preserve_semantic_distinctions_and_sink_refusal`
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
///
/// # Specification
/// - requires: the payload is interpreted in the named wire coordinate or
///   framing role.
/// - ensures: retains raw bytes or the carried quantity without claiming that a
///   decoder will admit it; canonicality is established by complete encoding or
///   validated decoding.
/// - panics: none.
/// - executable: none — this wire carrier has no invocation boundary; byte
///   projection, framing and reader validation carry its executable
///   obligations.
///
/// # Adequacy
/// - hypothesis: L3 observes byte/range boundaries and complete mixed-field
///   images; L2 compares varint bytes with an independent arithmetic reference.
///   Nominal role separation is L0. The carrier alone does not prove
///   canonicality or node admission.
/// - witness: `wire::tests::image_ranges_and_bytes_match_independent_projections`
/// - witness: `wire::tests::wire_fields_preserve_prefixes_and_little_endian_order`
/// - witness: `wire::tests::varints_match_a_quotient_reference_at_every_group_boundary`
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
    /// - requires: a formatter accepting or refusing writes.
    /// - ensures: writes the version as a decimal integer.
    /// - provides: the version value carried by an unsupported-version refusal.
    /// - fails: propagates the formatter write failure.
    /// - panics: none.
    /// - executable: none — Formatter exposes no readable output or
    ///   sink-refusal state; checking either here would require wrapping or
    ///   replaying the write.
    ///
    /// # Adequacy
    /// - hypothesis: L3 observes all byte-valued tag spellings, version
    ///   boundaries and a real exhausted byte sink. The assertions separate
    ///   radix, width, case, numeric truncation and swallowed refusal;
    ///   unrelated diagnostic prose is not pinned.
    /// - witness: `error::tests::diagnostics_preserve_semantic_distinctions_and_sink_refusal`
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
///
/// # Specification
/// - requires: the payload is interpreted in the named wire coordinate or
///   framing role.
/// - ensures: retains raw bytes or the carried quantity without claiming that a
///   decoder will admit it; canonicality is established by complete encoding or
///   validated decoding.
/// - panics: none.
/// - executable: none — this wire carrier has no invocation boundary; byte
///   projection, framing and reader validation carry its executable
///   obligations.
///
/// # Adequacy
/// - hypothesis: L3 observes byte/range boundaries and complete mixed-field
///   images; L2 compares varint bytes with an independent arithmetic reference.
///   Nominal role separation is L0. The carrier alone does not prove
///   canonicality or node admission.
/// - witness: `wire::tests::image_ranges_and_bytes_match_independent_projections`
/// - witness: `wire::tests::wire_fields_preserve_prefixes_and_little_endian_order`
/// - witness: `wire::tests::varints_match_a_quotient_reference_at_every_group_boundary`
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
///
/// # Specification
/// - requires: the payload is interpreted in the named wire coordinate or
///   framing role.
/// - ensures: retains raw bytes or the carried quantity without claiming that a
///   decoder will admit it; canonicality is established by complete encoding or
///   validated decoding.
/// - panics: none.
/// - executable: none — this wire carrier has no invocation boundary; byte
///   projection, framing and reader validation carry its executable
///   obligations.
///
/// # Adequacy
/// - hypothesis: L3 observes byte/range boundaries and complete mixed-field
///   images; L2 compares varint bytes with an independent arithmetic reference.
///   Nominal role separation is L0. The carrier alone does not prove
///   canonicality or node admission.
/// - witness: `wire::tests::image_ranges_and_bytes_match_independent_projections`
/// - witness: `wire::tests::wire_fields_preserve_prefixes_and_little_endian_order`
/// - witness: `wire::tests::varints_match_a_quotient_reference_at_every_group_boundary`
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
///
/// # Specification
/// - requires: the payload is interpreted in the named wire coordinate or
///   framing role.
/// - ensures: retains raw bytes or the carried quantity without claiming that a
///   decoder will admit it; canonicality is established by complete encoding or
///   validated decoding.
/// - panics: none.
/// - executable: none — this wire carrier has no invocation boundary; byte
///   projection, framing and reader validation carry its executable
///   obligations.
///
/// # Adequacy
/// - hypothesis: L3 observes byte/range boundaries and complete mixed-field
///   images; L2 compares varint bytes with an independent arithmetic reference.
///   Nominal role separation is L0. The carrier alone does not prove
///   canonicality or node admission.
/// - witness: `wire::tests::image_ranges_and_bytes_match_independent_projections`
/// - witness: `wire::tests::wire_fields_preserve_prefixes_and_little_endian_order`
/// - witness: `wire::tests::varints_match_a_quotient_reference_at_every_group_boundary`
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 observes zero, a small count and the executing target
    ///   ceiling through the numeric projection. These distinguish truncation
    ///   and offset substitution; saturation on pointers wider than 64 bits is
    ///   outside the tested platform.
    /// - witness: `wire::tests::wire_fields_preserve_prefixes_and_little_endian_order`
    #[spec(
        ensures: |ret| ret.0 == u64::try_from(value.0).unwrap_or(u64::MAX),
    )]
    #[inline]
    fn from(value: WireUsize) -> Self
    {
        Self(u64::try_from(value.0).unwrap_or(u64::MAX))
    }
}

/// An offset into an artifact image, and the length of one.
///
/// # Specification
/// - requires: the payload is interpreted in the named wire coordinate or
///   framing role.
/// - ensures: retains raw bytes or the carried quantity without claiming that a
///   decoder will admit it; canonicality is established by complete encoding or
///   validated decoding.
/// - panics: none.
/// - executable: none — this wire carrier has no invocation boundary; byte
///   projection, framing and reader validation carry its executable
///   obligations.
///
/// # Adequacy
/// - hypothesis: L3 observes byte/range boundaries and complete mixed-field
///   images; L2 compares varint bytes with an independent arithmetic reference.
///   Nominal role separation is L0. The carrier alone does not prove
///   canonicality or node admission.
/// - witness: `wire::tests::image_ranges_and_bytes_match_independent_projections`
/// - witness: `wire::tests::wire_fields_preserve_prefixes_and_little_endian_order`
/// - witness: `wire::tests::varints_match_a_quotient_reference_at_every_group_boundary`
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
///
/// # Specification
/// - requires: the payload is interpreted in the named wire coordinate or
///   framing role.
/// - ensures: retains raw bytes or the carried quantity without claiming that a
///   decoder will admit it; canonicality is established by complete encoding or
///   validated decoding.
/// - panics: none.
/// - executable: none — this wire carrier has no invocation boundary; byte
///   projection, framing and reader validation carry its executable
///   obligations.
///
/// # Adequacy
/// - hypothesis: L3 observes byte/range boundaries and complete mixed-field
///   images; L2 compares varint bytes with an independent arithmetic reference.
///   Nominal role separation is L0. The carrier alone does not prove
///   canonicality or node admission.
/// - witness: `wire::tests::image_ranges_and_bytes_match_independent_projections`
/// - witness: `wire::tests::wire_fields_preserve_prefixes_and_little_endian_order`
/// - witness: `wire::tests::varints_match_a_quotient_reference_at_every_group_boundary`
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
///
/// # Specification
/// - requires: the payload is interpreted in the named wire coordinate or
///   framing role.
/// - ensures: retains raw bytes or the carried quantity without claiming that a
///   decoder will admit it; canonicality is established by complete encoding or
///   validated decoding.
/// - panics: none.
/// - executable: none — this wire carrier has no invocation boundary; byte
///   projection, framing and reader validation carry its executable
///   obligations.
///
/// # Adequacy
/// - hypothesis: L3 observes byte/range boundaries and complete mixed-field
///   images; L2 compares varint bytes with an independent arithmetic reference.
///   Nominal role separation is L0. The carrier alone does not prove
///   canonicality or node admission.
/// - witness: `wire::tests::image_ranges_and_bytes_match_independent_projections`
/// - witness: `wire::tests::wire_fields_preserve_prefixes_and_little_endian_order`
/// - witness: `wire::tests::varints_match_a_quotient_reference_at_every_group_boundary`
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

/// Borrowed candidate artifact bytes offered to the validating decoder.
///
/// # Specification
/// - requires: the payload is interpreted in the named wire coordinate or
///   framing role.
/// - ensures: retains raw bytes or the carried quantity without claiming that a
///   decoder will admit it; canonicality is established by complete encoding or
///   validated decoding.
/// - panics: none.
/// - executable: none — this wire carrier has no invocation boundary; byte
///   projection, framing and reader validation carry its executable
///   obligations.
///
/// # Adequacy
/// - hypothesis: L3 observes byte/range boundaries and complete mixed-field
///   images; L2 compares varint bytes with an independent arithmetic reference.
///   Nominal role separation is L0. The carrier alone does not prove
///   canonicality or node admission.
/// - witness: `wire::tests::image_ranges_and_bytes_match_independent_projections`
/// - witness: `wire::tests::wire_fields_preserve_prefixes_and_little_endian_order`
/// - witness: `wire::tests::varints_match_a_quotient_reference_at_every_group_boundary`
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 enumerates all ordered and reversed endpoint pairs
    ///   through one past a four-byte image, plus the usize ceiling and empty
    ///   input. Exact byte sequences distinguish shifted ranges, inclusive
    ///   ends, lost high bits and inverted-range acceptance; the independent
    ///   iterator projection does not call the production slicing method.
    /// - witness: `wire::tests::image_ranges_and_bytes_match_independent_projections`
    #[spec(
        ensures: |ret| ret.as_ref().map(|image| image.0) == self.0.get(range.start.0 .. range.end.0),
    )]
    #[inline]
    #[must_use]
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
    ///
    /// # Adequacy
    /// - hypothesis: L3 enumerates all ordered and reversed endpoint pairs
    ///   through one past a four-byte image, plus the usize ceiling and empty
    ///   input. Exact byte sequences distinguish shifted ranges, inclusive
    ///   ends, lost high bits and inverted-range acceptance; the independent
    ///   iterator projection does not call the production slicing method.
    /// - witness: `wire::tests::image_ranges_and_bytes_match_independent_projections`
    #[spec(
        ensures: |ret| ret.map(|byte| byte.0) == self.0.get(offset.0).copied(),
    )]
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

/// An owned encoder byte image, possibly incomplete during construction.
///
/// It is the encoder's only output type and the unit the canonical-form
/// comparison is stated over: an artifact is canonical exactly when re-encoding
/// what it decoded reproduces the same [`EncodedArtifact`].
///
/// # Specification
/// - requires: the payload is interpreted in the named wire coordinate or
///   framing role.
/// - ensures: retains raw bytes or the carried quantity without claiming that a
///   decoder will admit it; canonicality is established by complete encoding or
///   validated decoding.
/// - panics: none.
/// - executable: none — this wire carrier has no invocation boundary; byte
///   projection, framing and reader validation carry its executable
///   obligations.
///
/// # Adequacy
/// - hypothesis: L3 observes byte/range boundaries and complete mixed-field
///   images; L2 compares varint bytes with an independent arithmetic reference.
///   Nominal role separation is L0. The carrier alone does not prove
///   canonicality or node admission.
/// - witness: `wire::tests::image_ranges_and_bytes_match_independent_projections`
/// - witness: `wire::tests::wire_fields_preserve_prefixes_and_little_endian_order`
/// - witness: `wire::tests::varints_match_a_quotient_reference_at_every_group_boundary`
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 compares mixed-field output with a literal byte
    ///   sequence for empty and nonempty prefixes, a version with unequal bytes
    ///   and zero/maximal versions. L3 observes unchanged prior bytes and exact
    ///   suffixes, separating endian reversal, width changes and prefix damage.
    /// - witness: `wire::tests::wire_fields_preserve_prefixes_and_little_endian_order`
    #[spec(
        captures: prefix = self.0.len(),
        ensures: |ret| self.0.len() == prefix.saturating_add(2)
                && self.0.get(prefix ..) == Some(version.0.to_le_bytes().as_slice()),
    )]
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
    /// - hypothesis: L2 compares every value from zero through 16384 and the
    ///   adjacent values at each seven-bit boundary with an independent
    ///   base-128 quotient/remainder reference, observing complete bytes after
    ///   a nonempty prefix. L3 pinned images include zero, 127, 128 and the u64
    ///   ceiling. Round trips are supplementary self-agreement, not the
    ///   minimality oracle.
    /// - witness: `wire::tests::uvarint_images_are_minimal_at_the_boundaries`
    /// - witness: `wire::tests::varints_match_a_quotient_reference_at_every_group_boundary`
    /// - witness: `wire::tests::uvarint_round_trips_through_the_reader`
    ///
    /// [`decode`]: mod@crate::decode
    #[spec(
        captures: prefix = self.0.len(),
        ensures: |ret| self.0.get(prefix ..).is_some_and(|bytes| { let width = if value.0 == 0 { 1 }
            else { 64u32.saturating_sub(value.0.leading_zeros()).div_ceil(7) };
            bytes.len() == usize::try_from(width).unwrap_or(usize::MAX)
                && bytes.iter().enumerate().all(|(index, &byte)| { let shift = u32::try_from(index).unwrap_or(u32::MAX).saturating_mul(7);
            u64::from(byte & 0x7f) == (value.0.checked_shr(shift).unwrap_or(0) & 0x7f)
                && (byte & 0x80 != 0) == (index.saturating_add(1) < bytes.len()) }) }),
    )]

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

    #[test]
    fn image_ranges_and_bytes_match_independent_projections()
    {
        let payload = [0u8, 127, 128, 255];
        for bytes in [payload.as_slice(), &[]] {
            let image = super::ArtifactImage::from(bytes);
            for start in [0usize, 1, 2, 3, 4, 5, usize::MAX] {
                assert_eq!(
                    bytes
                        .iter()
                        .enumerate()
                        .find(|&(index, _)| index == start)
                        .map(|(_, &byte)| byte),
                    image.byte_at(super::ByteOffset(start)).map(|byte| byte.0)
                );
                for end in [0usize, 1, 2, 3, 4, 5, usize::MAX] {
                    let expected = (start <= end && end <= bytes.len()).then(|| {
                        bytes
                            .iter()
                            .skip(start)
                            .take(end.saturating_sub(start))
                            .copied()
                            .collect::<Vec<_>>()
                    });
                    let actual = image
                        .span(super::ByteOffset(start) .. super::ByteOffset(end))
                        .map(|part| part.as_ref().to_vec());
                    assert_eq!(expected, actual, "range {start}..{end}");
                }
            }
        }
    }

    #[test]
    fn wire_fields_preserve_prefixes_and_little_endian_order()
    {
        let mut out = EncodedArtifact::new();
        out.put_image(super::ArtifactImage::from([0xdeu8, 0xad].as_slice()));
        out.put_version(super::FormatVersion(0x1234));
        out.put_tag(super::WireTag(0xa5));
        out.put_image(super::ArtifactImage::from([0u8, 255].as_slice()));
        out.put_uvarint(WireU64(128));
        assert_eq!(
            [0xde, 0xad, 0x34, 0x12, 0xa5, 0, 255, 0x80, 1].as_slice(),
            out.as_ref()
        );
        let mut limits = EncodedArtifact::new();
        limits.put_version(super::FormatVersion(0));
        limits.put_version(super::FormatVersion(u16::MAX));
        assert_eq!([0u8, 0, 255, 255].as_slice(), limits.as_ref());
        for value in [0usize, 1, usize::MAX] {
            let expected = u128::try_from(value)
                .expect("pointer width fits u128")
                .min(u128::from(u64::MAX));
            assert_eq!(
                expected,
                u128::from(super::WireU64::from(super::WireUsize(value)).0)
            );
        }
    }

    #[test]
    fn varints_match_a_quotient_reference_at_every_group_boundary()
    {
        let check = |value: u64| {
            let mut expected = vec![0xa5u8];
            let mut quotient = value;
            loop {
                let digit = u8::try_from(quotient.rem_euclid(128)).expect("base-128 digit");
                quotient = quotient.div_euclid(128);
                expected.push(if quotient == 0 {
                    digit
                }
                else {
                    digit.saturating_add(128)
                });
                if quotient == 0 {
                    break;
                }
            }
            let mut actual = EncodedArtifact::new();
            actual.put_tag(super::WireTag(0xa5));
            actual.put_uvarint(WireU64(value));
            assert_eq!(expected.as_slice(), actual.as_ref(), "value {value}");
        };
        for value in 0u64 ..= 0x4000 {
            check(value);
        }
        for shift in [14u32, 21, 28, 35, 42, 49, 56, 63] {
            let boundary = 1u64.checked_shl(shift).expect("shift below 64");
            for value in [
                boundary.saturating_sub(1),
                boundary,
                boundary.saturating_add(1),
            ] {
                if value > 0x4000 {
                    check(value);
                }
            }
        }
        check(u64::MAX);
    }
}
