//! The two checks of a string's invariants over bytes: whether a range is
//! valid UTF-8, and where its first zero byte is, the byte that ends a C
//! string.

use crate::Byte;
use crate::Found;
use crate::Position;
use crate::Range;
use crate::Utf8;

/// Whether `range` is valid UTF-8, with the position of its first fault.
///
/// # Safety
///
/// - unsafe invariants: the bytes of `range` are readable where it is not
///   empty, and no write to them happens during the call.
///
/// # Specification
/// - ensures: `Valid` when the range is a whole sequence of valid UTF-8, an
///   empty range included; else `Fault(p)`, where the bytes before `p` are
///   valid UTF-8 and the sequence that starts at `p` is not valid, or the range
///   ends inside it.
/// - panics: none.
/// - time: one pass over the range.
/// - executable: none — the bytes are the memory itself.
///
/// # Adequacy
/// - hypothesis: L2 — the bytes `61 62 FF` give the position 2; an empty range,
///   a whole sequence of four bytes, a sequence that the range cuts, a
///   surrogate, and an overlong form each give their own answer.
/// - witness: `tests::check::the_check_of_utf8_gives_the_first_fault`
#[inline]
#[must_use]
pub unsafe fn check_utf8(range: Range) -> Utf8
{
    // SAFETY: the caller's invariants hold for the range.
    let bytes = unsafe { crate::bytes(range).0 };
    match core::str::from_utf8(bytes) {
        Ok(_) => Utf8::Valid,
        Err(fault) => Utf8::Fault(Position(fault.valid_up_to())),
    }
}

/// The first zero byte of `range`. A range holds no zero byte, so it can be
/// the bytes of a C string before its terminator, when this gives `Absent`.
///
/// # Safety
///
/// - unsafe invariants: the bytes of `range` are readable where it is not
///   empty, and no write to them happens during the call.
///
/// # Specification
/// - ensures: `At(p)` for the least `p` whose byte is zero; `Absent` when no
///   byte of the range is zero, an empty range included.
/// - panics: none.
/// - time: one pass over the range, at most.
/// - executable: none — the bytes are the memory itself.
///
/// # Adequacy
/// - hypothesis: L2 — an empty range, one zero byte, a range whose only zero is
///   its last byte, and a range with no zero.
/// - witness: `tests::check::a_zero_byte_is_found_where_a_c_string_ends`
#[inline]
#[must_use]
pub unsafe fn find_zero(range: Range) -> Found
{
    // SAFETY: the caller's invariants hold for the range.
    unsafe { crate::search::find_byte(range, Byte(0)) }
}
