//! The content pointer — the value plane's whole address vocabulary.
//!
//! A [`ContentPtr`] is stable, portable and independent of any process: it
//! names a position inside a value by naming the chunk that holds it and the
//! token offset within that chunk. Nothing about the process, the insertion
//! order or the machine that produced it enters the address.

use core::fmt;

use anodized::spec;

use crate::error::ValueError;
use crate::error::ValueQuantity;

/// The byte length of a [`ChunkDigest`]: one BLAKE3 output.
pub const CHUNK_DIGEST_LEN: usize = 0x20_usize;

/// The BLAKE3 identity of one framed chunk image.
///
/// Deliberately not the record plane's node identity, and no conversion is
/// offered in either direction: the two planes hash different byte languages
/// under different domains, and a shared digest type would invite handing a
/// chunk digest to a node validator.
#[repr(transparent)]
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ChunkDigest([u8; CHUNK_DIGEST_LEN]);

impl From<[u8; CHUNK_DIGEST_LEN]> for ChunkDigest
{
    /// Wraps raw digest bytes without computing anything.
    ///
    /// The digest is claimed by whoever wraps it; nothing here checks that the
    /// bytes hash any image. The claim is checked where it matters, by
    /// [`crate::verify_chunk_image`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: [u8; CHUNK_DIGEST_LEN]) -> Self
    {
        Self(bytes)
    }
}

impl AsRef<[u8]> for ChunkDigest
{
    /// Borrows the digest bytes.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn as_ref(&self) -> &[u8]
    {
        self.0.as_slice()
    }
}

impl fmt::Display for ChunkDigest
{
    /// Writes the digest as lowercase hexadecimal.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes exactly two lowercase hexadecimal digits per byte, in
    ///   byte order, and nothing else.
    /// - provides: the rendering a refusal names a chunk by.
    /// - fails: propagates the formatter's own write failure unchanged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 only — the rendering is separated from any other by one
    ///   digest whose hexadecimal is asserted exactly, with a leading zero
    ///   nibble that a width-less rendering would drop.
    /// - witness: `ptr::tests::a_digest_renders_lowercase_hexadecimal`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        for byte in self.0 {
            write!(f, "{byte:02x}")?;
        }

        Ok(())
    }
}

impl fmt::Debug for ChunkDigest
{
    /// Writes the digest as [`fmt::Display`] does.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        fmt::Display::fmt(self, f)
    }
}

/// A token index inside one chunk's body.
///
/// The offset is within the chunk, never within the whole value: that is what
/// keeps a pointer stable when an unrelated part of the value changes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TokenOffset(u32);

impl TokenOffset
{
    /// The first record of a body.
    pub const ZERO: Self = Self(0_u32);

    /// Returns the offset one record later, refusing one past the width.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `|ret| ret.is_ok() == (self.0 < u32::MAX)` — the successor
    ///   exactly when it fits.
    /// - provides: the step a reader and a writer advance by per record.
    /// - fails: [`ValueError::ArithmeticOverflow`] naming the token offset.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError::ArithmeticOverflow`] — the offset is already `u32::MAX`.
    #[inline]
    #[spec(ensures: |ret| ret.is_ok() == (self.0 < u32::MAX))]
    pub fn next(self) -> Result<Self, ValueError>
    {
        self.0
            .checked_add(1_u32)
            .map(Self)
            .ok_or(ValueError::ArithmeticOverflow {
                quantity: ValueQuantity::TokenOffset,
            })
    }
}

impl From<u32> for TokenOffset
{
    /// Reads a `u32` as a token offset.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(offset: u32) -> Self
    {
        Self(offset)
    }
}

impl From<TokenOffset> for u32
{
    /// Reads the offset back out.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(offset: TokenOffset) -> Self
    {
        offset.0
    }
}

impl fmt::Display for TokenOffset
{
    /// Writes the offset as a number.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the carried number through the `u32` rendering.
    /// - provides: the position a refusal names.
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

/// A content pointer: a chunk digest and a token offset inside that chunk.
///
/// The pair is the whole address. A holder can fetch and verify the chunk,
/// then read the value rooted at the offset, with no reference to the store it
/// came from beyond the store being able to answer for the digest.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ContentPtr
{
    /// The chunk holding the addressed subtree.
    digest: ChunkDigest,
    /// The token index of the subtree's root within that chunk.
    offset: TokenOffset,
}

impl ContentPtr
{
    /// Pairs a chunk digest with a token offset inside that chunk.
    ///
    /// # Specification
    /// - requires: nothing; an offset that does not name a constructor of the
    ///   chunk is refused when the chunk is read, not here.
    /// - ensures: the pointer carries both fields unchanged.
    /// - provides: the plane's only address constructor.
    /// - fails: never.
    /// - panics: none.
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| ret.digest == digest && ret.offset == offset)]
    pub fn new(
        digest: ChunkDigest,
        offset: TokenOffset,
    ) -> Self
    {
        Self { digest, offset }
    }

    /// Returns the addressed chunk's digest.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn digest(&self) -> ChunkDigest
    {
        self.digest
    }

    /// Returns the token offset within the addressed chunk.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn offset(&self) -> TokenOffset
    {
        self.offset
    }
}

#[cfg(test)]
mod tests
{
    use alloc::string::ToString as _;

    use super::ChunkDigest;

    #[test]
    fn a_digest_renders_lowercase_hexadecimal()
    {
        let mut bytes = [0_u8; 32];
        bytes[0] = 0x0A;
        bytes[31] = 0xFF;

        assert_eq!(
            ChunkDigest::from(bytes).to_string(),
            "0a000000000000000000000000000000000000000000000000000000000000ff"
        );
    }
}
