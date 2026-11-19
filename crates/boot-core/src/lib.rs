//! The operations on a range of bytes that allocate nothing: a copy, a move,
//! a fill, a comparison, two searches, and the checks of UTF-8 and of a zero
//! byte. The crate is of the layer `boot`, outside the integrity and the
//! validity walls: it checks no term and keeps no value of the store.
//!
//! The data core needs these operations before gandr states them itself.
//! Rust's own are generic, so the direct call of Rust cannot name them. Each
//! function here takes each range as an address and a length: a [`Range`]
//! that it reads, or a [`Place`] that it writes. It reads or writes that
//! range alone. A search gives a [`Found`], and the check of UTF-8 gives a
//! [`Utf8`]. No function allocates, and no function panics.
//!
//! A crate of the layer `boot` is a stage of the bootstrap. A twin in gandr
//! replaces it, so each public function has no generic parameter and states
//! the clauses that the twin meets.
//!
//! # References
//!
//! - `vault:01a1ebc5-2ff2-7833-b871-85901e734925` — newest: the data core of
//!   the bootstrap (§ boot-data-crates, § boot-data-strings): the rules of a
//!   crate of the layer `boot`, the line of the allocation between this crate
//!   and `boot-data`, and the two invariants of a string as checks over bytes.

#![no_std]

mod block;
mod check;
mod search;

pub use crate::block::compare;
pub use crate::block::copy;
pub use crate::block::fill;
pub use crate::block::move_bytes;
pub use crate::check::check_utf8;
pub use crate::check::find_zero;
pub use crate::search::find_byte;
pub use crate::search::find_range;

/// A count of bytes: the length of a range.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Length(pub usize);

/// The offset of a byte from the base of its range.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Position(pub usize);

/// One byte: a `u8` on each host, with no sign.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Byte(pub u8);

/// A range of bytes that a function reads: the address of its first byte and
/// its length. An empty range can have any address, null too.
///
/// # Specification
/// trivial.
#[repr(C)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Range
{
    /// The address of the first byte.
    pub base: *const u8,
    /// The count of the bytes.
    pub length: Length,
}

impl From<&[u8]> for Range
{
    /// The range of the bytes of a slice.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: &[u8]) -> Self
    {
        Self {
            base: bytes.as_ptr(),
            length: Length(bytes.len()),
        }
    }
}

/// A range of bytes that a function writes: the address of its first byte and
/// its length. An empty place can have any address, null too.
///
/// # Specification
/// trivial.
#[repr(C)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Place
{
    /// The address of the first byte.
    pub base: *mut u8,
    /// The count of the bytes.
    pub length: Length,
}

impl From<&mut [u8]> for Place
{
    /// The place of the bytes of a slice.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(bytes: &mut [u8]) -> Self
    {
        Self {
            base: bytes.as_mut_ptr(),
            length: Length(bytes.len()),
        }
    }
}

/// The answer of a search: the position of the first match, or an absence
/// when no position matches.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Found
{
    /// The first match starts at this position.
    At(Position),
    /// No position matches.
    Absent,
}

/// The answer of the check of UTF-8.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Utf8
{
    /// Each byte of the range is part of a whole, valid sequence.
    Valid,
    /// The first sequence that is not valid, or that the range cuts, starts
    /// at this position. Each byte before it is valid UTF-8.
    Fault(Position),
}

/// A write that the place cannot hold: the source is longer than the place.
/// The function writes no byte.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Short;

/// The bytes of a range, as a slice whose lifetime the caller states.
///
/// # Specification
/// trivial.
#[repr(transparent)]
struct Bytes<'range>(&'range [u8]);

/// The bytes of `range`.
///
/// # Safety
///
/// - unsafe invariants: when the range is not empty, its bytes are readable and
///   no write to them happens while the slice lives.
///
/// # Specification
/// - ensures: an empty slice for an empty range, whatever its address; each
///   other range's bytes in order.
/// - panics: none.
/// - executable: none — the slice is the memory itself.
///
/// # Adequacy
/// - hypothesis: L2 — an empty range with a null address is read as no bytes,
///   and a range that ends at the end of a page reads no byte past it.
/// - witness: `tests::block::an_empty_range_compares_equal_at_any_address`
/// - witness: `tests::search::a_search_to_the_end_of_a_page_reads_no_byte_past_it`
const unsafe fn bytes<'range>(range: Range) -> Bytes<'range>
{
    if range.length.0 == 0 {
        return Bytes(&[]);
    }
    // SAFETY: the caller's invariants hold for the range's bytes, and a range
    // that is not empty has a readable, so not null, address.
    Bytes(unsafe { core::slice::from_raw_parts(range.base, range.length.0) })
}
