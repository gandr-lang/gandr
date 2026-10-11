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
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on one dense 32-byte digest observes the complete
    ///   lowercase hexadecimal golden and exact write failures at allowances 0,
    ///   1, 31 and 63. It distinguishes reordered or omitted bytes, lost zero
    ///   nibbles, uppercase digits and swallowed errors; it is not an
    ///   exhaustive digest or formatter-mode domain.
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
    /// - requires: nothing.
    /// - ensures: writes the same lowercase hexadecimal image as Display.
    /// - provides: the digest identity in diagnostic structures.
    /// - fails: propagates the formatter's write failure unchanged.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on one dense digest observes the complete hexadecimal
    ///   golden and exact refusals at allowances 0, 1, 31 and 63,
    ///   distinguishing added wrappers, substituted bytes and swallowed errors.
    ///   Other digests and formatting modes are outside this fixed witness
    ///   domain.
    /// - witness: `ptr::tests::a_digest_renders_lowercase_hexadecimal`
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
    /// - ensures: success is exactly one greater than the input; only the
    ///   maximum offset fails, with the token-offset overflow quantity.
    /// - provides: the step a reader and a writer advance by per record.
    /// - fails: [`ValueError::ArithmeticOverflow`] naming the token offset.
    /// - panics: none.
    ///
    /// # Errors
    /// [`ValueError::ArithmeticOverflow`] — the offset is already `u32::MAX`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 on zero, byte and two-byte carry boundaries, and the
    ///   last two offsets observes exact successors and the typed overflow. It
    ///   distinguishes a skipped step, narrowed counter, wraparound or wrong
    ///   refusal quantity; interior offsets are sampled, not exhaustive.
    /// - witness: `ptr::tests::offset_successors_preserve_carries_and_refuse_overflow`
    #[inline]
    #[spec(ensures: |ret| match ret {
        Ok(next) => next.0.checked_sub(1) == Some(self.0),
        Err(ValueError::ArithmeticOverflow { quantity: ValueQuantity::TokenOffset }) => self.0 == u32::MAX,
        Err(_) => false,
    })]
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
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Errors
    /// Propagates the formatter's write failure.
    ///
    /// # Adequacy
    /// - hypothesis: L2 on zero, 37 and the u32 ceiling compares signed,
    ///   zero-padded decimal output with the primitive; L3 observes a refusing
    ///   sink's exact error. The matrix distinguishes changed values, dropped
    ///   flags and swallowed errors, not every formatting mode.
    /// - witness: `ptr::tests::offsets_preserve_rendering_flags_and_refusal`
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
    ///
    /// # Adequacy
    /// - hypothesis: L2 on two independently framed pair bodies addresses their
    ///   four leaves at offsets 1 and 4 and observes each exact decoded word.
    ///   This distinguishes substituted chunk identities, zeroed or shifted
    ///   offsets; arbitrary digests and invalid offsets are outside this
    ///   constructor witness's domain.
    /// - witness: `tests::values::known_interior_addresses_select_distinct_values`
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

    use anodized::spec;

    use super::ChunkDigest;
    use super::TokenOffset;
    use crate::ValueError;
    use crate::ValueQuantity;

    /// A sink that refuses writes exceeding its remaining byte allowance.
    #[repr(transparent)]
    #[derive(Debug)]
    struct RefusingSink(usize);

    impl core::fmt::Write for RefusingSink
    {
        /// Consumes an admitted write's allowance; refuses a larger write.
        ///
        /// # Specification
        /// - requires: nothing; empty text is admitted even at zero allowance.
        /// - ensures: success subtracts the text length; refusal leaves the
        ///   allowance unchanged.
        /// - provides: failures at the beginning and inside a digest rendering.
        /// - fails: the formatting error when text exceeds the allowance.
        /// - panics: none.
        ///
        /// # Errors
        /// The formatting error when the text does not fit.
        ///
        /// # Adequacy
        /// - hypothesis: L3 on digest writes with allowances 0, 1, 31 and 63
        ///   observes exact refusal; the enforced state relation distinguishes
        ///   accepting an overrun or charging a refused write. This does not
        ///   prescribe the formatter's write segmentation.
        /// - witness: `ptr::tests::a_digest_renders_lowercase_hexadecimal`
        #[spec(
            captures: before = self.0,
            ensures: |ret| match before.checked_sub(s.len()) {
                Some(remaining) => ret == Ok(()) && self.0 == remaining,
                None => ret == Err(core::fmt::Error) && self.0 == before,
            },
        )]
        fn write_str(
            &mut self,
            s: &str,
        ) -> core::fmt::Result
        {
            let Some(remaining) = self.0.checked_sub(s.len())
            else {
                return Err(core::fmt::Error);
            };
            self.0 = remaining;
            Ok(())
        }
    }

    #[test]
    fn a_digest_renders_lowercase_hexadecimal()
    {
        let bytes = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
            0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b,
            0x1c, 0x1d, 0x1e, 0xff,
        ];
        let digest = ChunkDigest::from(bytes);
        let expected = "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1eff";
        assert_eq!(digest.to_string(), expected);
        assert_eq!(alloc::format!("{digest:?}"), expected);
        for allowance in [0, 1, 31, 63] {
            assert_eq!(
                core::fmt::write(&mut RefusingSink(allowance), format_args!("{digest}")),
                Err(core::fmt::Error),
            );
            assert_eq!(
                core::fmt::write(&mut RefusingSink(allowance), format_args!("{digest:?}")),
                Err(core::fmt::Error),
            );
        }
    }

    #[test]
    fn offsets_preserve_rendering_flags_and_refusal()
    {
        for value in [0, 37, u32::MAX] {
            let offset = TokenOffset::from(value);
            assert_eq!(
                alloc::format!("{offset:+012}"),
                alloc::format!("{value:+012}")
            );
            assert_eq!(
                core::fmt::write(&mut RefusingSink(0), format_args!("{offset}")),
                Err(core::fmt::Error),
            );
        }
    }

    #[test]
    fn offset_successors_preserve_carries_and_refuse_overflow()
    {
        for (value, successor) in [
            (0, 1),
            (0xff, 0x100),
            (0xffff, 0x1_0000),
            (u32::MAX - 1, u32::MAX),
        ] {
            assert_eq!(
                TokenOffset::from(value).next(),
                Ok(TokenOffset::from(successor))
            );
        }
        assert_eq!(
            TokenOffset::from(u32::MAX).next(),
            Err(ValueError::ArithmeticOverflow {
                quantity: ValueQuantity::TokenOffset,
            })
        );
    }
}
