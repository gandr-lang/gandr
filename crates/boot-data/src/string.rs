//! The string buffer: a vector of bytes that are valid UTF-8, with one zero
//! byte after the last byte.
//!
//! The check of UTF-8 of `boot-core` stands at each way in: an append checks
//! its bytes before it writes one, and a vector becomes a string buffer only
//! when its bytes pass the check. So each byte that stands is part of a whole,
//! valid sequence. The zero byte after the last byte lets a reader of C take
//! the bytes with no copy. A buffer with no byte holds no block, and its bytes
//! with the zero are one static zero byte.

use core::fmt;

use gandr_boot_alloc::Heap;
use gandr_boot_alloc::Refused;
use gandr_boot_core::Byte;
use gandr_boot_core::Length;
use gandr_boot_core::Position;
use gandr_boot_core::Range;
use gandr_boot_core::Utf8;
use gandr_boot_core::check_utf8;

use crate::vector::Refusal;
use crate::vector::Vector;

/// The zero byte that ends the bytes of a buffer with no block.
static ZERO: u8 = 0;

/// A write that the string buffer does not make. The buffer keeps its bytes.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Rejected
{
    /// The bytes are not valid UTF-8: the first sequence that is not valid,
    /// or that the bytes cut, starts at this position of them.
    Utf8(Position),
    /// The vector cannot grow to hold the bytes and the zero after them.
    Growth(Refusal),
}

impl fmt::Display for Rejected
{
    /// Writes the cause of the rejection.
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
            Self::Utf8(at) => write!(f, "write: the bytes are not UTF-8 from position {}", at.0),
            Self::Growth(refusal) => write!(f, "write: {refusal}"),
        }
    }
}

impl core::error::Error for Rejected
{
}

/// A vector that does not become a string buffer, and the cause. The vector
/// keeps its bytes.
///
/// # Specification
/// trivial.
#[derive(Debug)]
pub struct Unchecked<'heap>
{
    /// The vector, as it was.
    pub vector: Vector<'heap>,
    /// The cause.
    pub rejected: Rejected,
}

/// A string buffer in a block of one heap: one linear owner of bytes that are
/// valid UTF-8, with one zero byte after the last byte.
///
/// The buffer lives no longer than its heap. The end of the buffer gives its
/// block back to the heap, and [`StringBuffer::release`] does the same and
/// gives the answer of the heap.
///
/// # Specification
/// - invariant: the bytes of [`StringBuffer::range`] are valid UTF-8; the
///   vector holds no block, or it holds those bytes and one zero byte after
///   them.
#[derive(Debug)]
pub struct StringBuffer<'heap>
{
    /// The bytes and the zero after them, or no block.
    bytes: Vector<'heap>,
}

impl<'heap> StringBuffer<'heap>
{
    /// A string buffer in `heap` that holds no byte and no block.
    ///
    /// # Specification
    /// - ensures: the length is zero, and the heap gives no block.
    /// - panics: none.
    /// - executable: none — the function asks the heap for nothing.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a buffer with no byte reads as an empty range, and
    ///   its bytes with the zero are one zero byte.
    /// - witness: `tests::string::an_empty_buffer_is_one_zero_byte`
    #[must_use]
    #[inline]
    pub const fn new(heap: &'heap Heap) -> Self
    {
        Self {
            bytes: Vector::new(heap),
        }
    }

    /// The count of the bytes of the text, with no zero after them.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn length(&self) -> Length
    {
        Length(self.bytes.length().0.saturating_sub(1))
    }

    /// The bytes of the text, as a range that `boot-core` reads. They are
    /// valid UTF-8. The range stays valid until the next call that takes the
    /// buffer by an exclusive reference.
    ///
    /// # Specification
    /// - ensures: the range of the bytes of the text in the order of their
    ///   appends, with no zero after them; an empty range with a null address
    ///   when the buffer has no block.
    /// - panics: none.
    /// - executable: none — the range is the memory itself.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the bytes of each append stand in order, through a
    ///   growth past one size class.
    /// - witness: `tests::string::each_append_stands_in_order_with_a_zero_after_it`
    #[must_use]
    #[inline]
    pub const fn range(&self) -> Range
    {
        Range {
            base: self.bytes.range().base,
            length: self.length(),
        }
    }

    /// The bytes of the text and the zero byte after them, as a reader of C
    /// takes them. The range stays valid until the next call that takes the
    /// buffer by an exclusive reference.
    ///
    /// # Specification
    /// - ensures: the range of [`StringBuffer::range`] and one zero byte after
    ///   it; one static zero byte when the buffer has no block.
    /// - panics: none.
    /// - executable: none — the range is the memory itself.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the last byte of the range is zero after each append,
    ///   and for a buffer with no block.
    /// - witness: `tests::string::an_empty_buffer_is_one_zero_byte`
    /// - witness: `tests::string::each_append_stands_in_order_with_a_zero_after_it`
    #[must_use]
    #[inline]
    pub fn terminated(&self) -> Range
    {
        let range = self.bytes.range();
        if range.length.0 == 0 {
            return Range {
                base: &raw const ZERO,
                length: Length(1),
            };
        }
        range
    }

    /// Writes the bytes of `from` after the last byte of the text, when they
    /// are valid UTF-8.
    ///
    /// # Safety
    ///
    /// - unsafe invariants: the bytes of `from` are readable where it is not
    ///   empty, no write to them happens during the call, and no byte of it is
    ///   a byte of the block of the buffer.
    ///
    /// # Specification
    /// - requires: no byte of `from` is a byte of the block of the buffer.
    /// - ensures: the text is the text before and the bytes of `from`, and one
    ///   zero byte follows it; or a rejection, with the buffer unchanged.
    /// - panics: none.
    /// - executable: none — the bytes are the memory itself.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — appends of sequences of one to four bytes stand in
    ///   order; bytes that are not UTF-8, and bytes that cut a sequence at
    ///   their end, are rejected at the position of the fault, and the buffer
    ///   keeps its bytes; an empty range adds nothing.
    /// - witness: `tests::string::each_append_stands_in_order_with_a_zero_after_it`
    /// - witness: `tests::string::bytes_that_are_not_utf8_are_rejected_where_they_fail`
    ///
    /// # Errors
    /// [`Rejected::Utf8`] at the first fault of `from`, or [`Rejected::Growth`]
    /// when the vector cannot grow.
    ///
    /// # Cost
    /// - time: linear in the length of `from`: one check and one copy, with the
    ///   cost of one growth.
    #[inline]
    pub unsafe fn append(
        &mut self,
        from: Range,
    ) -> Result<(), Rejected>
    {
        if from.length.0 == 0 {
            return Ok(());
        }
        // SAFETY: the caller states that `from` is readable and unwritten.
        if let Utf8::Fault(at) = unsafe { check_utf8(from) } {
            return Err(Rejected::Utf8(at));
        }
        let text = self.length();
        let zero = usize::from(self.bytes.length().0 == 0);
        self.bytes
            .reserve(Length(from.length.0.saturating_add(zero)))
            .map_err(Rejected::Growth)?;
        self.bytes.truncate(text);
        // SAFETY: the caller states that `from` is readable and shares no byte
        // with the block, and the room for it is reserved.
        unsafe { self.bytes.append(from) }.map_err(Rejected::Growth)?;
        self.bytes.push(Byte(0)).map_err(Rejected::Growth)
    }

    /// The string buffer of the bytes of `vector`, when they are valid UTF-8.
    ///
    /// # Specification
    /// - ensures: a buffer whose text is the bytes of `vector`, with one zero
    ///   byte after them in the same block; or the vector, unchanged, and the
    ///   rejection.
    /// - panics: none.
    /// - executable: none — the heap decides what it grants.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a vector of valid bytes becomes a buffer with the
    ///   same text, and a vector with a fault comes back with its bytes and the
    ///   position of the fault.
    /// - witness: `tests::string::a_vector_becomes_a_buffer_when_its_bytes_are_utf8`
    ///
    /// # Errors
    /// [`Unchecked`] with [`Rejected::Utf8`] at the first fault, or with
    /// [`Rejected::Growth`] when the vector cannot grow by the zero byte.
    #[inline]
    pub fn from_vector(mut vector: Vector<'heap>) -> Result<Self, Unchecked<'heap>>
    {
        if vector.length().0 == 0 {
            return Ok(Self { bytes: vector });
        }
        // SAFETY: the range is the bytes that stand in the vector, which is
        // held here and not written during the check.
        if let Utf8::Fault(at) = unsafe { check_utf8(vector.range()) } {
            return Err(Unchecked {
                vector,
                rejected: Rejected::Utf8(at),
            });
        }
        match vector.push(Byte(0)) {
            Ok(()) => Ok(Self { bytes: vector }),
            Err(refusal) => Err(Unchecked {
                vector,
                rejected: Rejected::Growth(refusal),
            }),
        }
    }

    /// The bytes of the text, as a vector in the same block, with no zero
    /// after them. The proof of UTF-8 is forgotten, and no byte is copied.
    ///
    /// # Specification
    /// - ensures: a vector whose bytes are the bytes of the text.
    /// - panics: none.
    /// - executable: none — the bytes are the memory itself.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the vector of a buffer holds the bytes of its text at
    ///   the address of the block of the buffer.
    /// - witness: `tests::string::a_vector_becomes_a_buffer_when_its_bytes_are_utf8`
    #[must_use]
    #[inline]
    pub fn into_vector(mut self) -> Vector<'heap>
    {
        let text = self.length();
        self.bytes.truncate(text);
        self.bytes
    }

    /// Gives the block back to the heap, and gives the answer of the heap.
    ///
    /// # Specification
    /// - ensures: as [`Vector::release`].
    /// - panics: none.
    /// - executable: none — the heap decides what it frees.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — as [`Vector::release`].
    /// - witness: `tests::string::an_empty_buffer_is_one_zero_byte`
    ///
    /// # Errors
    /// The refusal of the heap's free.
    #[inline]
    pub fn release(self) -> Result<(), Refused>
    {
        self.bytes.release()
    }
}
