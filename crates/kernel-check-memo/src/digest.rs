//! The content digest and the deciding comparison beneath it.
//!
//! A digest is a **positive fast path only**. Different digests prove that two
//! supports differ; equal digests prove nothing and hand off to the deciding
//! comparison over the supports' canonical content. A memo that let a digest
//! decide agreement would answer for the wrong support on a collision, which is
//! the one failure a memo must not admit — a silent false agreement.
//!
//! This module owns no encoding. The consumer computes the digest from its own
//! canonical content encoding and hands the words over; the seam only carries
//! them and uses them to pick the bucket a deciding comparison then scans.

/// One 64-bit word of a [`ContentDigest`].
///
/// Opaque on purpose: the consumer chooses the hash, and nothing in the seam
/// interprets the bits. Ordering is over the raw word so that a memo's bucket
/// map has a deterministic iteration order.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DigestWord(u64);

impl From<u64> for DigestWord
{
    /// The digest word carrying `value` unchanged.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: u64) -> Self
    {
        Self(value)
    }
}

impl From<DigestWord> for u64
{
    /// The raw word `value` carries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: DigestWord) -> Self
    {
        value.0
    }
}

/// The digest of a support's canonical content encoding.
///
/// Two words rather than one because the seam's bucket map degrades to a linear
/// scan under collision, and the consumer that wants a wider digest should not
/// have to fold it down to a machine word to hand it over.
///
/// # Specification
/// - requires: the consumer derives both words from the *content* of the
///   support — never from an arena position, an allocation order, or any other
///   datum that does not survive relocation.
/// - ensures: two supports with equal content produce equal digests, given a
///   deterministic consumer digest.
/// - provides: the fast path that selects a bucket; never a decision. This
///   stays prose: content derivation is an obligation on the consumer, equal
///   digests for equal content is a law over two values, and a data-item
///   `#[spec]` states an invariant of one value that the pinned expansion never
///   checks at construction.
/// - panics: none.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ContentDigest
{
    /// The high word, compared first so ordering is lexicographic over the
    /// pair as a whole.
    high: DigestWord,
    /// The low word.
    low: DigestWord,
}

impl ContentDigest
{
    /// Builds the digest carrying `high` and `low` unchanged.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        high: DigestWord,
        low: DigestWord,
    ) -> Self
    {
        Self { high, low }
    }

    /// The high word.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn high(self) -> DigestWord
    {
        self.high
    }

    /// The low word.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn low(self) -> DigestWord
    {
        self.low
    }
}

/// The verdict of the deciding comparison two supports hand off to.
///
/// This is the relation a memo actually serves on. A digest narrows the search
/// to a bucket; this decides. Naming it separately from the digest is what
/// makes the positive-fast-path-only discipline expressible rather than merely
/// documented: a memo implementation that never consults this value cannot type
/// check.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ContentAgreement
{
    /// The two supports have the same content, so one may answer for the other.
    Agree,
    /// The two supports differ, so neither may answer for the other — however
    /// their digests compare.
    Differ,
}
