//! The buffer: the bytes that move into a submission and come back with its
//! completion. Only this module reads the bytes, so no signature of the
//! crate holds a slice of them.

use std::fs::File;
use std::os::unix::fs::FileExt as _;

use crate::ring::Moved;
use crate::ring::Position;
use crate::sys::Errno;
use crate::sys::Word;

/// The bytes that an operation writes from or reads into. The `Io` owns
/// the buffer from its submission to its completion, and the completion
/// gives it back.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Buffer(Vec<u8>);

impl From<Vec<u8>> for Buffer
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: Vec<u8>) -> Self
    {
        Self(bytes)
    }
}

impl From<Buffer> for Vec<u8>
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(buffer: Buffer) -> Self
    {
        buffer.0
    }
}

impl Buffer
{
    /// The address of the first byte, for an entry that reads from it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn address(&self) -> Word
    {
        Word::from(self.0.as_ptr().expose_provenance())
    }

    /// The address of the first byte, for an entry that writes into it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn address_mut(&mut self) -> Word
    {
        Word::from(self.0.as_mut_ptr().expose_provenance())
    }

    /// The count of bytes, at most `u32::MAX`, as an entry carries it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn length(&self) -> Moved
    {
        Moved::from(u32::try_from(self.0.len()).unwrap_or(u32::MAX))
    }

    /// Read from `file` at `at` into the buffer, by one positioned read.
    ///
    /// # Specification
    /// - ensures: on `Ok`, the count of bytes read, at most the buffer's
    ///   length.
    /// - fails: the error number of the read.
    /// - panics: none.
    /// - executable: none — the file is the kernel's.
    ///
    /// # Errors
    /// The error number that the read answers.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the blocking form reads back the bytes that a linked
    ///   write wrote.
    /// - witness: `tests::io::a_linked_write_sync_and_read_complete_in_order`
    #[inline]
    pub fn read_from(
        &mut self,
        file: &File,
        at: Position,
    ) -> Result<Moved, Errno>
    {
        file.read_at(&mut self.0, u64::from(at))
            .map(|read| Moved::from(u32::try_from(read).unwrap_or(u32::MAX)))
            .map_err(Errno::from)
    }

    /// Write the buffer into `file` at `at`, by one positioned write.
    ///
    /// # Specification
    /// - ensures: on `Ok`, the count of bytes written, at most the buffer's
    ///   length.
    /// - fails: the error number of the write.
    /// - panics: none.
    /// - executable: none — the file is the kernel's.
    ///
    /// # Errors
    /// The error number that the write answers.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the blocking form's write fails on a file open to
    ///   read alone, and cancels the sync linked to it.
    /// - witness: `tests::io::a_failed_write_cancels_its_linked_sync`
    #[inline]
    pub fn write_into(
        &self,
        file: &File,
        at: Position,
    ) -> Result<Moved, Errno>
    {
        file.write_at(&self.0, u64::from(at))
            .map(|written| Moved::from(u32::try_from(written).unwrap_or(u32::MAX)))
            .map_err(Errno::from)
    }
}
