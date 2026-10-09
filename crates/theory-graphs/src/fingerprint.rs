//! The fixed FNV-1a accumulator every stable fingerprint in the crate, and in
//! its consumers, is computed with.
//!
//! The parameters are FNV-1a's published 64-bit offset basis and prime, so a
//! fingerprint depends only on the bytes absorbed: never on a process-seeded
//! hasher, a compiler version, or the host's byte order.

use crate::Fingerprint;
use crate::FingerprintByte;
use crate::FingerprintBytes;
use crate::FingerprintWord16;
use crate::FingerprintWord32;
use crate::FingerprintWord64;

/// FNV-1a 64-bit offset basis.
const FNV_OFFSET: u64 = 0xcbf2_9ce4_8422_2325;

/// FNV-1a 64-bit prime.
const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;

/// A 64-bit FNV-1a accumulator: absorbs a byte stream in order and reports
/// the hash of everything absorbed.
///
/// # Adequacy
/// - hypothesis: L3 pointwise — the empty stream and the published `"a"` test
///   vector pin both parameters, and each word width is pinned against the same
///   bytes absorbed one at a time in little-endian order.
/// - witness: `fingerprint::tests::published_vectors_pin_the_parameters`
/// - witness: `fingerprint::tests::words_absorb_little_endian`
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Fnv64
{
    /// The hash of the bytes absorbed so far.
    state: u64,
}

impl Default for Fnv64
{
    /// Starts an accumulator at the offset basis.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn default() -> Self
    {
        Self::new()
    }
}

impl Fnv64
{
    /// Starts an accumulator at the offset basis.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new() -> Self
    {
        Self { state: FNV_OFFSET }
    }

    /// Absorbs one byte.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the state becomes `(state ^ byte) * prime`, wrapping.
    /// - provides: the one mixing step every other write is built from.
    /// - panics: none.
    #[inline]
    pub fn write_byte<B>(
        &mut self,
        byte: B,
    ) where
        B: Into<FingerprintByte>,
    {
        self.state ^= u64::from(u8::from(byte.into()));
        self.state = self.state.wrapping_mul(FNV_PRIME);
    }

    /// Absorbs a 16-bit word, low byte first.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: equals absorbing the word's two little-endian bytes in order.
    /// - panics: none.
    #[inline]
    pub fn write_u16<W>(
        &mut self,
        value: W,
    ) where
        W: Into<FingerprintWord16>,
    {
        for byte in u16::from(value.into()).to_le_bytes() {
            self.write_byte(byte);
        }
    }

    /// Absorbs a 32-bit word, low byte first.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: equals absorbing the word's four little-endian bytes in
    ///   order.
    /// - panics: none.
    #[inline]
    pub fn write_u32<W>(
        &mut self,
        value: W,
    ) where
        W: Into<FingerprintWord32>,
    {
        for byte in u32::from(value.into()).to_le_bytes() {
            self.write_byte(byte);
        }
    }

    /// Absorbs a 64-bit word, low byte first.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: equals absorbing the word's eight little-endian bytes in
    ///   order.
    /// - panics: none.
    #[inline]
    pub fn write_u64<W>(
        &mut self,
        value: W,
    ) where
        W: Into<FingerprintWord64>,
    {
        for byte in u64::from(value.into()).to_le_bytes() {
            self.write_byte(byte);
        }
    }

    /// Absorbs a run of bytes in order, without a length frame.
    ///
    /// # Specification
    /// - requires: nothing; a caller that needs the run delimited writes its
    ///   length first.
    /// - ensures: equals absorbing each byte in order.
    /// - panics: none.
    #[inline]
    pub fn write_bytes<'bytes, B>(
        &mut self,
        bytes: B,
    ) where
        B: Into<FingerprintBytes<'bytes>>,
    {
        for &byte in bytes.into().as_ref() {
            self.write_byte(byte);
        }
    }

    /// Reports the hash of everything absorbed.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn finish(self) -> Fingerprint
    {
        Fingerprint::from(self.state)
    }
}

#[cfg(test)]
mod tests
{
    use super::*;

    #[test]
    fn published_vectors_pin_the_parameters()
    {
        assert_eq!(u64::from(Fnv64::new().finish()), 0xcbf2_9ce4_8422_2325_u64);
        let mut a = Fnv64::new();
        a.write_byte(b'a');
        assert_eq!(u64::from(a.finish()), 0xaf63_dc4c_8601_ec8c_u64);
        let mut foobar = Fnv64::new();
        foobar.write_bytes(b"foobar");
        assert_eq!(u64::from(foobar.finish()), 0x8594_4171_f739_67e8_u64);
    }

    #[test]
    fn words_absorb_little_endian()
    {
        let mut words = Fnv64::new();
        words.write_u16(0x0201_u16);
        words.write_u32(0x0605_0403_u32);
        words.write_u64(0x0e0d_0c0b_0a09_0807_u64);
        let mut bytes = Fnv64::new();
        bytes.write_bytes(&[1_u8, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]);
        assert_eq!(words.finish(), bytes.finish());
    }
}
