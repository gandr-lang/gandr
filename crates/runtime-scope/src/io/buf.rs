//! The lent buffer: bytes that the caller lends an operation for the scope's
//! life.

use ::core::ops::Deref;
use ::core::ops::DerefMut;

use crate::completion::Count;

/// Bytes that the caller lends an operation for the scope's life, through
/// the region's allocator. The borrow `'tsk` holds them until the scope
/// ends, so no caller reads them while the kernel writes them.
#[repr(transparent)]
#[derive(Debug, Eq, PartialEq)]
pub struct Buf<'tsk>(&'tsk mut [u8]);

impl<'tsk> From<&'tsk mut [u8]> for Buf<'tsk>
{
    /// The buffer of `bytes`.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn from(bytes: &'tsk mut [u8]) -> Self
    {
        Self(bytes)
    }
}

impl Deref for Buf<'_>
{
    type Target = [u8];

    /// The buffer's bytes.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn deref(&self) -> &[u8]
    {
        self.0
    }
}

impl DerefMut for Buf<'_>
{
    /// The buffer's bytes, to write.
    ///
    /// # Specification
    ///
    /// trivial.
    #[inline]
    fn deref_mut(&mut self) -> &mut [u8]
    {
        self.0
    }
}

impl Buf<'_>
{
    /// The buffer's first `count` bytes: the bytes that an operation wrote.
    ///
    /// # Specification
    ///
    /// - provides: the prefix of `count` bytes, with the borrow `'tsk`.
    /// - fails: `None` when `count` is past the buffer's length.
    /// - panics: none.
    /// - executable: none — the prefix is the standard library's slice.
    ///
    /// # Adequacy
    ///
    /// - hypothesis: L3 — a receive of four bytes into eight gives the four.
    /// - witness: `io::socket::test::socket::recv`
    /// - witness: `completion::test::cqe::a_count_prefixes_the_lent_buffer`
    #[inline]
    #[must_use]
    pub fn prefix(
        self,
        count: Count,
    ) -> Option<Self>
    {
        self.0.get_mut(.. usize::from(count)).map(Self)
    }
}
