//! The buffer: the bytes that move into a submission and come back with its
//! completion, in the allocator that the caller names. Only this module
//! reads the bytes, so no signature of the crate holds a slice of them.
//!
//! A buffer that a ring registers carries its slot in that ring's table,
//! and the ring reads and writes it by the slot. Any other ring, and the
//! blocking form, read and write the same bytes by their address.

use alloc::vec::Vec;
use core::alloc::Allocator;
use std::fs::File;
use std::os::unix::fs::FileExt as _;

use crate::ring::Moved;
use crate::ring::Position;
use crate::sys::Errno;
use crate::sys::Word;

/// The tables of fixed buffers and of fixed files of one ring: no two rings
/// of the process share one.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Table(pub u64);

/// A buffer's place in its ring's table of fixed buffers.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Slot(pub u16);

/// A file's place in its ring's table of fixed files.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct FileSlot(pub u32);

/// The byte that [`Buffer::fill`] writes into each byte of a buffer.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Fill(pub u8);

/// The bytes that an operation writes from or reads into, in the allocator
/// `A`.
///
/// The `Io` owns the buffer from its submission to its completion, and the
/// completion gives it back. No operation grows a buffer, so its bytes never
/// move.
///
/// # Specification
/// trivial.
#[derive(Clone)]
pub struct Buffer<A>
where
    A: Allocator,
{
    /// The bytes.
    bytes: Vec<u8, A>,
    /// The table that registers the bytes, and their slot in it.
    fixed: Option<(Table, Slot)>,
}

impl<A> core::fmt::Debug for Buffer<A>
where
    A: Allocator,
{
    /// The buffer's length and its slot, if a table registers it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result
    {
        f.debug_struct("Buffer")
            .field("length", &self.bytes.len())
            .field("fixed", &self.fixed)
            .finish()
    }
}

impl<A, B> PartialEq<Buffer<B>> for Buffer<A>
where
    A: Allocator,
    B: Allocator,
{
    /// Whether the two buffers hold the same bytes, wherever they live.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn eq(
        &self,
        other: &Buffer<B>,
    ) -> bool
    {
        self.bytes.as_slice() == other.bytes.as_slice()
    }
}

impl<A> Eq for Buffer<A> where A: Allocator
{
}

impl<A> From<Vec<u8, A>> for Buffer<A>
where
    A: Allocator,
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: Vec<u8, A>) -> Self
    {
        Self { bytes, fixed: None }
    }
}

impl<A> From<Buffer<A>> for Vec<u8, A>
where
    A: Allocator,
{
    /// # Specification
    /// trivial.
    #[inline]
    fn from(buffer: Buffer<A>) -> Self
    {
        buffer.bytes
    }
}

impl<A> Buffer<A>
where
    A: Allocator,
{
    /// A buffer of `length` zero bytes in `allocator`, or none when the
    /// allocator refuses the bytes.
    ///
    /// # Specification
    /// - ensures: on `Some`, a buffer of `length` bytes, each zero, that no
    ///   table registers.
    /// - panics: none.
    /// - executable: none — the allocator's answer is its own.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an allocator that holds one buffer refuses the
    ///   registration of two.
    /// - witness: `tests::io::a_register_past_the_budget_is_refused`
    #[inline]
    pub fn zeroed(
        length: Moved,
        allocator: A,
    ) -> Option<Self>
    {
        let length = usize::try_from(u32::from(length)).ok()?;
        let mut bytes = Vec::new_in(allocator);
        bytes.try_reserve_exact(length).ok()?;
        bytes.resize(length, 0);
        Some(Self { bytes, fixed: None })
    }

    /// Mark this buffer as registered in `table` at `slot`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub const fn mark(
        &mut self,
        table: Table,
        slot: Slot,
    )
    {
        self.fixed = Some((table, slot));
    }

    /// Set each byte of the buffer to `byte`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn fill(
        &mut self,
        byte: Fill,
    )
    {
        self.bytes.fill(byte.0);
    }

    /// The buffer's slot in `table`, when `table` registers it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn slot_in(
        &self,
        table: Table,
    ) -> Option<Slot>
    {
        let (registered, slot) = self.fixed?;
        (registered == table).then_some(slot)
    }

    /// The address of the first byte, for an entry that reads from it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn address(&self) -> Word
    {
        Word::from(self.bytes.as_ptr().expose_provenance())
    }

    /// The address of the first byte, for an entry that writes into it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn address_mut(&mut self) -> Word
    {
        Word::from(self.bytes.as_mut_ptr().expose_provenance())
    }

    /// The count of bytes, at most `u32::MAX`, as an entry carries it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn length(&self) -> Moved
    {
        Moved::from(u32::try_from(self.bytes.len()).unwrap_or(u32::MAX))
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
        file.read_at(&mut self.bytes, u64::from(at))
            .map(|read| Moved::from(u32::try_from(read).unwrap_or(u32::MAX)))
            .map_err(Errno::from)
    }

    /// Write the first `kept` bytes of the buffer into `file` at `at`, by
    /// one positioned write.
    ///
    /// # Specification
    /// - ensures: on `Ok`, the count of bytes written, at most `kept` and the
    ///   buffer's length.
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
        kept: Moved,
    ) -> Result<Moved, Errno>
    {
        let kept = usize::try_from(u32::from(kept)).unwrap_or(usize::MAX);
        let bytes = self.bytes.get(.. kept).unwrap_or(&self.bytes);
        file.write_at(bytes, u64::from(at))
            .map(|written| Moved::from(u32::try_from(written).unwrap_or(u32::MAX)))
            .map_err(Errno::from)
    }

    /// Flip each bit of the byte at `at`, if the buffer holds it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub fn flip(
        &mut self,
        at: Moved,
    )
    {
        if let Some(byte) = usize::try_from(u32::from(at))
            .ok()
            .and_then(|at| self.bytes.get_mut(at))
        {
            *byte ^= 0xff_u8;
        }
    }
}
