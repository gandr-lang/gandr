//! The vector of bytes: a block of the heap, its capacity and its length.
//!
//! The first `length` bytes of the block stand, and the rest of the block has
//! no claim on its bytes. A push writes the byte after the last one and moves
//! the length. A growth asks the heap for a block of twice the capacity, or of
//! the bytes that the growth needs when they are more, and the heap moves the
//! bytes that stand. The capacity is each byte that the heap grants, so a
//! block of a size class is used whole.

use core::alloc::Layout;
use core::fmt;
use core::ptr;

use gandr_boot_alloc::Base;
use gandr_boot_alloc::Heap;
use gandr_boot_alloc::Refused;
use gandr_boot_core::Byte;
use gandr_boot_core::Length;
use gandr_boot_core::Position;
use gandr_boot_core::Range;

/// The least capacity of a vector that holds a byte: the smallest size class
/// of the heap, so the first block is used whole.
const LEAST: usize = 16;

/// A growth that the vector cannot make. The vector keeps its bytes, its
/// length and its capacity.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Refusal
{
    /// The bytes that the growth needs are more than a layout holds: more
    /// than `isize::MAX`.
    Size,
    /// The heap refuses the block.
    Heap(Refused),
}

impl fmt::Display for Refusal
{
    /// Writes the cause of the refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Size => f.write_str("grow: the bytes are more than a layout holds"),
            Self::Heap(refused) => write!(f, "grow: {refused}"),
        }
    }
}

impl core::error::Error for Refusal
{
}

/// A vector of bytes in a block of one heap: one linear owner of its bytes.
///
/// The vector lives no longer than its heap. A vector that holds no byte and
/// has no capacity holds no block. The end of the vector gives its block back
/// to the heap. [`Vector::release`] does the same and gives the answer of the
/// heap.
///
/// # Specification
/// trivial.
#[derive(Debug)]
pub struct Vector<'heap>
{
    /// The heap of the block.
    heap: &'heap Heap,
    /// The first byte of the block, or no block while the capacity is zero.
    base: Option<Base>,
    /// The bytes of the block.
    capacity: usize,
    /// The bytes that stand, at the start of the block.
    length: usize,
}

impl<'heap> Vector<'heap>
{
    /// A vector in `heap` that holds no byte and no block.
    ///
    /// # Specification
    /// - ensures: the length and the capacity are zero, and the heap gives no
    ///   block.
    /// - panics: none.
    /// - executable: none — the function asks the heap for nothing.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a vector with no byte reads as an empty range, and a
    ///   read at each position gives an absence.
    /// - witness: `tests::vector::an_empty_vector_holds_no_block`
    #[must_use]
    #[inline]
    pub const fn new(heap: &'heap Heap) -> Self
    {
        Self {
            heap,
            base: None,
            capacity: 0,
            length: 0,
        }
    }

    /// The count of the bytes that stand.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn length(&self) -> Length
    {
        Length(self.length)
    }

    /// The count of the bytes of the block: the length that the vector holds
    /// with no growth.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn capacity(&self) -> Length
    {
        Length(self.capacity)
    }

    /// The bytes that stand, as a range that `boot-core` reads. The range
    /// stays valid until the next call that takes the vector by an exclusive
    /// reference.
    ///
    /// # Specification
    /// - ensures: the range of the first `length` bytes of the block, in the
    ///   order of their pushes; an empty range with a null address when the
    ///   vector has no block.
    /// - panics: none.
    /// - executable: none — the range is the memory itself.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — each pushed byte reads back at its position, through
    ///   a growth from one size class to the next and to whole pages.
    /// - witness: `tests::vector::each_pushed_byte_stands_in_order`
    #[must_use]
    #[inline]
    pub const fn range(&self) -> Range
    {
        Range {
            base: match self.base {
                Some(base) => base.0.as_ptr().cast_const(),
                None => ptr::null(),
            },
            length: Length(self.length),
        }
    }

    /// The byte at `position`.
    ///
    /// # Specification
    /// - ensures: the byte at `position` when it is before the length; an
    ///   absence otherwise.
    /// - panics: none.
    /// - executable: `ret.is_some() == (position.0 < length)`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the last byte reads back, and the position of the
    ///   length gives an absence.
    /// - witness: `tests::vector::each_pushed_byte_stands_in_order`
    /// - witness: `tests::vector::an_empty_vector_holds_no_block`
    #[must_use]
    #[inline]
    pub fn byte(
        &self,
        position: Position,
    ) -> Option<Byte>
    {
        if position.0 >= self.length {
            return None;
        }
        let at = self.base?.0.as_ptr().wrapping_add(position.0);
        // SAFETY: the position is before the length, so the byte stands in
        // the block.
        Some(Byte(unsafe { at.read() }))
    }

    /// Makes room for `more` bytes after the length.
    ///
    /// # Specification
    /// - ensures: the capacity is at least the length and `more`; the bytes
    ///   that stand are unchanged; a capacity that is already enough asks the
    ///   heap for nothing; or a refusal, with the vector unchanged.
    /// - panics: none.
    /// - executable: none — the heap decides what it grants.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a room that is already enough keeps the address of
    ///   the block, and a room past the size of a layout is refused with the
    ///   vector unchanged.
    /// - witness: `tests::vector::a_room_within_the_capacity_keeps_the_block`
    /// - witness: `tests::vector::a_room_past_a_layout_is_refused`
    ///
    /// # Errors
    /// [`Refusal::Size`] when the length and `more` are more than a layout
    /// holds, or [`Refusal::Heap`] when the heap refuses the block.
    ///
    /// # Cost
    /// - time: constant with no growth; a growth costs the heap's allocation
    ///   and a copy of the bytes of the block.
    #[inline]
    pub fn reserve(
        &mut self,
        more: Length,
    ) -> Result<(), Refusal>
    {
        let needed = self.length.checked_add(more.0).ok_or(Refusal::Size)?;
        if needed <= self.capacity {
            return Ok(());
        }
        let doubled = self.capacity.saturating_mul(2);
        let wanted = needed.max(doubled).max(LEAST);
        let layout = Layout::from_size_align(wanted, 1)
            .or_else(|_doubled| Layout::from_size_align(needed, 1))
            .map_err(|_layout| Refusal::Size)?;
        let granted = match self.base {
            None => self.heap.allocate(layout),
            Some(base) => {
                let old =
                    Layout::from_size_align(self.capacity, 1).map_err(|_layout| Refusal::Size)?;
                // SAFETY: the heap gave the block for a layout of the
                // capacity, the new layout is larger, and no reference into
                // the block lives while the vector is lent exclusively.
                unsafe { self.heap.grow(base, old, layout) }
            },
        }
        .map_err(Refusal::Heap)?;
        self.base = Some(granted.base());
        self.capacity = granted.0.len();
        Ok(())
    }

    /// Writes `byte` after the last byte that stands.
    ///
    /// # Specification
    /// - ensures: the length grows by one, and the byte at the old length is
    ///   `byte`; each byte before it is unchanged; or a refusal of
    ///   [`Vector::reserve`], with the vector unchanged.
    /// - panics: none.
    /// - executable: none — the heap decides what it grants.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — each of 100,000 pushed bytes reads back at its
    ///   position, through each size class of the heap and whole pages.
    /// - witness: `tests::vector::each_pushed_byte_stands_in_order`
    ///
    /// # Errors
    /// A refusal of [`Vector::reserve`].
    ///
    /// # Cost
    /// - time: constant, amortised over the doubling growth.
    #[inline]
    pub fn push(
        &mut self,
        byte: Byte,
    ) -> Result<(), Refusal>
    {
        self.reserve(Length(1))?;
        let at = self
            .base
            .ok_or(Refusal::Size)?
            .0
            .as_ptr()
            .wrapping_add(self.length);
        // SAFETY: the room of one byte after the length is in the block.
        unsafe {
            at.write(byte.0);
        }
        self.length = self.length.wrapping_add(1);
        Ok(())
    }

    /// Writes the bytes of `from` after the last byte that stands.
    ///
    /// # Safety
    ///
    /// - unsafe invariants: the bytes of `from` are readable where it is not
    ///   empty, no write to them happens during the call, and no byte of it is
    ///   a byte of the block of the vector.
    ///
    /// # Specification
    /// - requires: no byte of `from` is a byte of the block of the vector.
    /// - ensures: the length grows by the length of `from`, and the bytes after
    ///   the old length are the bytes of `from` in order; each byte before them
    ///   is unchanged; or a refusal of [`Vector::reserve`], with the vector
    ///   unchanged.
    /// - panics: none.
    /// - executable: none — the bytes are the memory itself.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — an append after pushed bytes keeps them and adds its
    ///   own, and an empty range with a null address adds nothing.
    /// - witness: `tests::vector::an_append_keeps_the_bytes_before_it`
    ///
    /// # Errors
    /// A refusal of [`Vector::reserve`].
    ///
    /// # Cost
    /// - time: linear in the length of `from`, with the cost of one growth.
    #[inline]
    pub unsafe fn append(
        &mut self,
        from: Range,
    ) -> Result<(), Refusal>
    {
        if from.length.0 == 0 {
            return Ok(());
        }
        self.reserve(from.length)?;
        let at = self
            .base
            .ok_or(Refusal::Size)?
            .0
            .as_ptr()
            .wrapping_add(self.length);
        // SAFETY: the room after the length holds `from.length` bytes, and
        // the caller states that `from` is readable and shares no byte with
        // the block.
        unsafe {
            ptr::copy_nonoverlapping(from.base, at, from.length.0);
        }
        self.length = self.length.wrapping_add(from.length.0);
        Ok(())
    }

    /// Keeps the first `length` bytes and ends the others.
    ///
    /// # Specification
    /// - ensures: the length is the smaller of `length` and the old length; the
    ///   bytes before it and the capacity are unchanged.
    /// - panics: none.
    /// - executable: `self.length() == min(length, old length)`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a cut keeps the first bytes, a cut past the length
    ///   changes nothing, and a push after a cut writes at the new length.
    /// - witness: `tests::vector::a_cut_keeps_the_first_bytes`
    #[inline]
    pub fn truncate(
        &mut self,
        length: Length,
    )
    {
        self.length = self.length.min(length.0);
    }

    /// Gives the block back to the heap, and gives the answer of the heap.
    ///
    /// # Specification
    /// - ensures: the heap holds the block as free, or the heap's refusal; a
    ///   vector with no block asks the heap for nothing.
    /// - panics: none.
    /// - executable: none — the heap decides what it frees.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a release of a block of whole pages and of a vector
    ///   with no block each give no refusal.
    /// - witness: `tests::vector::a_release_gives_the_block_back`
    ///
    /// # Errors
    /// The refusal of the heap's free.
    #[inline]
    pub fn release(mut self) -> Result<(), Refused>
    {
        self.free()
    }

    /// Gives the block back to the heap, and leaves the vector with no block.
    ///
    /// # Specification
    /// trivial.
    fn free(&mut self) -> Result<(), Refused>
    {
        let Some(base) = self.base.take()
        else {
            return Ok(());
        };
        let capacity = core::mem::take(&mut self.capacity);
        self.length = 0;
        let Ok(layout) = Layout::from_size_align(capacity, 1)
        else {
            return Ok(());
        };
        // SAFETY: the heap gave the block for a layout of the capacity, and
        // the vector, which holds the only reference into it, ends with it.
        unsafe { self.heap.free(base, layout) }
    }
}

impl Drop for Vector<'_>
{
    /// Gives the block back to the heap. A refusal of the heap has no
    /// receiver here; [`Vector::release`] gives it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn drop(&mut self)
    {
        let _freed: Result<(), Refused> = self.free();
    }
}
