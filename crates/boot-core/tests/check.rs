//! The two checks against each subject: UTF-8, and the first zero byte.

use gandr_boot_core::Found;
use gandr_boot_core::Position;
use gandr_boot_core::Range;
use gandr_boot_core::Utf8;

use crate::harness::NOWHERE;
use crate::harness::SUBJECTS;

/// The check of UTF-8 gives the position of the first fault: 2 for the bytes
/// `61 62 FF`. An empty range and whole sequences of one to four bytes are
/// valid. A sequence that the range cuts, a lone byte of continuation, a
/// surrogate and an overlong form each fault where they start.
#[test]
fn the_check_of_utf8_gives_the_first_fault()
{
    let cases: [(&[u8], Utf8); 10] = [
        (&[0x61, 0x62, 0xFF], Utf8::Fault(Position(2))),
        (&[0x61], Utf8::Valid),
        (&[0xC3, 0xA9], Utf8::Valid),
        (&[0xE2, 0x82, 0xAC], Utf8::Valid),
        (&[0xF0, 0x9F, 0x98, 0x80], Utf8::Valid),
        (&[0xF0, 0x9F, 0x98], Utf8::Fault(Position(0))),
        (&[0x61, 0xE2, 0x82], Utf8::Fault(Position(1))),
        (&[0x80], Utf8::Fault(Position(0))),
        (&[0xED, 0xA0, 0x80], Utf8::Fault(Position(0))),
        (&[0xC0, 0x80], Utf8::Fault(Position(0))),
    ];
    for subject in &SUBJECTS {
        let name = subject.name;
        // SAFETY: an empty range is read as no bytes.
        let empty = unsafe { (subject.check_utf8)(NOWHERE) };
        assert_eq!(Utf8::Valid, empty, "{name}");
        for (bytes, answer) in cases {
            // SAFETY: the range is a live array.
            let checked = unsafe { (subject.check_utf8)(Range::from(bytes)) };
            assert_eq!(answer, checked, "{name}: {bytes:02X?}");
        }
    }
}

/// A zero byte is found where a C string ends: absent from an empty range and
/// from a range with no zero, at 0 in one zero byte and in two, and at the
/// last position of a range whose only zero ends it.
#[test]
fn a_zero_byte_is_found_where_a_c_string_ends()
{
    let cases: [(&[u8], Found); 4] = [
        (&[0], Found::At(Position(0))),
        (&[0, 0], Found::At(Position(0))),
        (b"ab\0", Found::At(Position(2))),
        (b"abc", Found::Absent),
    ];
    for subject in &SUBJECTS {
        let name = subject.name;
        // SAFETY: an empty range is read as no bytes.
        let empty = unsafe { (subject.find_zero)(NOWHERE) };
        assert_eq!(Found::Absent, empty, "{name}");
        for (bytes, found) in cases {
            // SAFETY: the range is a live array.
            let answer = unsafe { (subject.find_zero)(Range::from(bytes)) };
            assert_eq!(found, answer, "{name}: {bytes:?}");
        }
    }
}
