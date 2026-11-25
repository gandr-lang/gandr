//! The block operations: a copy between two ranges that share no byte, a move
//! between two ranges that can share bytes, a fill, and the comparison that
//! gives the order of two ranges.

use core::cmp::Ordering;

use crate::Byte;
use crate::Place;
use crate::Range;
use crate::Short;

/// Copies the bytes of `from` into the first bytes of `to`.
///
/// # Safety
///
/// - unsafe invariants: the bytes of `from` are readable and the bytes of `to`
///   are writable, where each is not empty; the two ranges share no byte.
///
/// # Specification
/// - requires: the two ranges share no byte.
/// - ensures: the first `from.length` bytes of `to` hold the bytes of `from` in
///   order, and the other bytes of `to` are unchanged; or `Short` when `to` is
///   shorter than `from`, with no byte written.
/// - panics: none.
/// - executable: none — the bytes are the memory itself.
///
/// # Adequacy
/// - hypothesis: L2 — a copy of an empty range, of one byte, and of a range
///   that ends at the end of a page; a copy into a place one byte too short
///   writes nothing.
/// - witness: `tests::block::a_copy_writes_the_source_and_keeps_the_rest`
///
/// # Errors
/// `Short` when `to` is shorter than `from`.
#[inline]
pub unsafe fn copy(
    to: Place,
    from: Range,
) -> Result<(), Short>
{
    if to.length < from.length {
        return Err(Short);
    }
    if from.length.0 == 0 {
        return Ok(());
    }
    // SAFETY: the caller's invariants hold for both ranges, which share no
    // byte, and `to` holds at least `from.length` bytes.
    unsafe {
        core::ptr::copy_nonoverlapping(from.base, to.base, from.length.0);
    }
    Ok(())
}

/// Moves the bytes of `from` into the first bytes of `to`. The two ranges can
/// share bytes: `to` then holds the bytes that `from` held before the move.
///
/// # Safety
///
/// - unsafe invariants: the bytes of `from` are readable and the bytes of `to`
///   are writable, where each is not empty.
///
/// # Specification
/// - ensures: the first `from.length` bytes of `to` hold the bytes that `from`
///   held before the call, in order, and the other bytes of `to` are unchanged;
///   or `Short` when `to` is shorter than `from`, with no byte written.
/// - panics: none.
/// - executable: none — the bytes are the memory itself.
///
/// # Adequacy
/// - hypothesis: L2 — a move forward and a move backward within one buffer,
///   each over shared bytes, give the source as it was; a move into a place too
///   short writes nothing.
/// - witness: `tests::block::a_move_over_shared_bytes_gives_the_source_as_it_was`
///
/// # Errors
/// `Short` when `to` is shorter than `from`.
#[inline]
pub unsafe fn move_bytes(
    to: Place,
    from: Range,
) -> Result<(), Short>
{
    if to.length < from.length {
        return Err(Short);
    }
    if from.length.0 == 0 {
        return Ok(());
    }
    // SAFETY: the caller's invariants hold for both ranges, and `to` holds at
    // least `from.length` bytes. `copy` admits ranges that share bytes.
    unsafe {
        core::ptr::copy(from.base, to.base, from.length.0);
    }
    Ok(())
}

/// Writes `byte` to each byte of `to`.
///
/// # Safety
///
/// - unsafe invariants: the bytes of `to` are writable, where it is not empty.
///
/// # Specification
/// - ensures: each byte of `to` is `byte`, and no byte outside it changes.
/// - panics: none.
/// - executable: none — the bytes are the memory itself.
///
/// # Adequacy
/// - hypothesis: L2 — a fill of an empty place, of one byte, and of a place
///   that ends at the end of a page; the bytes beside the place keep their
///   values.
/// - witness: `tests::block::a_fill_writes_each_byte_of_the_place_alone`
#[inline]
pub unsafe fn fill(
    to: Place,
    byte: Byte,
)
{
    if to.length.0 == 0 {
        return;
    }
    // SAFETY: the caller's invariants hold for the place's bytes.
    unsafe {
        core::ptr::write_bytes(to.base, byte.0, to.length.0);
    }
}

/// The order of `left` and `right` as sequences of bytes: the order of the
/// first byte where they differ, or of their lengths when one is the start of
/// the other.
///
/// # Safety
///
/// - unsafe invariants: the bytes of each range are readable where it is not
///   empty, and no write to them happens during the call.
///
/// # Specification
/// - ensures: `Less` when `left` comes first, `Greater` when `right` comes
///   first, and `Equal` when the two hold the same bytes; a byte compares as an
///   unsigned number.
/// - panics: none.
/// - executable: none — the bytes are the memory itself.
///
/// # Adequacy
/// - hypothesis: L2 — two empty ranges at any address, a range and its own
///   start, two ranges that differ at their last byte, and the byte `0x80`
///   against `0x7F`, which a signed comparison orders the other way.
/// - witness: `tests::block::an_empty_range_compares_equal_at_any_address`
/// - witness: `tests::block::a_comparison_orders_by_the_first_unequal_byte`
#[inline]
#[must_use]
pub unsafe fn compare(
    left: Range,
    right: Range,
) -> Ordering
{
    // SAFETY: the caller's invariants hold for both ranges.
    let left = unsafe { crate::bytes(left).0 };
    // SAFETY: as above.
    let right = unsafe { crate::bytes(right).0 };
    left.cmp(right)
}
