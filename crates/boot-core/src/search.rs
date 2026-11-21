//! The two searches: the first position of a byte in a range, and the first
//! position of a range in a range. Each gives an absence when no position
//! matches.

use crate::Byte;
use crate::Found;
use crate::Position;
use crate::Range;

/// The first position of `byte` in `range`.
///
/// # Safety
///
/// - unsafe invariants: the bytes of `range` are readable where it is not
///   empty, and no write to them happens during the call.
///
/// # Specification
/// - ensures: `At(p)` for the least `p` whose byte is `byte`; `Absent` when no
///   byte of the range is `byte`, an empty range included.
/// - panics: none.
/// - time: one pass over the range, at most.
/// - executable: none — the bytes are the memory itself.
///
/// # Adequacy
/// - hypothesis: L2 — a search of an empty range, of one byte, of a range whose
///   last byte is the first match, and of a range that ends at the end of a
///   page.
/// - witness: `tests::search::a_byte_is_found_at_its_first_position`
/// - witness: `tests::search::a_search_to_the_end_of_a_page_reads_no_byte_past_it`
#[inline]
#[must_use]
pub unsafe fn find_byte(
    range: Range,
    byte: Byte,
) -> Found
{
    // SAFETY: the caller's invariants hold for the range.
    let bytes = unsafe { crate::bytes(range).0 };
    bytes
        .iter()
        .position(|&each| each == byte.0)
        .map_or(Found::Absent, |at| Found::At(Position(at)))
}

/// The first position of `needle` in `range`.
///
/// # Safety
///
/// - unsafe invariants: the bytes of each range are readable where it is not
///   empty, and no write to them happens during the call.
///
/// # Specification
/// - ensures: `At(p)` for the least `p` where the bytes of `range` from `p` on
///   start with the bytes of `needle`; `At(0)` for an empty needle; `Absent`
///   when no position matches, and for a needle longer than the range.
/// - panics: none.
/// - time: at most the product of the two lengths, in the worst case.
/// - executable: none — the bytes are the memory itself.
///
/// # Adequacy
/// - hypothesis: L2 — an empty needle, a needle of one byte, a needle that
///   matches at the last position, a needle that matches in part before its
///   whole match, and a needle longer than the range.
/// - witness: `tests::search::a_range_is_found_at_its_first_whole_match`
#[inline]
#[must_use]
pub unsafe fn find_range(
    range: Range,
    needle: Range,
) -> Found
{
    // SAFETY: the caller's invariants hold for both ranges.
    let bytes = unsafe { crate::bytes(range).0 };
    // SAFETY: as above.
    let needle = unsafe { crate::bytes(needle).0 };
    if needle.is_empty() {
        return Found::At(Position(0));
    }
    bytes
        .windows(needle.len())
        .position(|window| window == needle)
        .map_or(Found::Absent, |at| Found::At(Position(at)))
}
