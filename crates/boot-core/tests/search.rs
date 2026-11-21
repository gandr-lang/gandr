//! The two searches against each subject, on an empty range, on one byte, and
//! on a range that ends at the end of a page.

use core::cmp::Ordering;

use gandr_boot_core::Byte;
use gandr_boot_core::Found;
use gandr_boot_core::Position;
use gandr_boot_core::Range;
use gandr_boot_core::Utf8;

use crate::harness::NOWHERE;
use crate::harness::SUBJECTS;
use crate::host::Guarded;

/// A byte is found at its first position: absent from an empty range, at 0
/// in one byte that matches, at its first of two positions, at the last
/// position, and absent from a range that holds it nowhere.
#[test]
fn a_byte_is_found_at_its_first_position()
{
    let cases: [(&[u8], u8, Found); 5] = [
        (&[3], 3, Found::At(Position(0))),
        (&[3], 4, Found::Absent),
        (&[1, 2, 3, 2], 2, Found::At(Position(1))),
        (&[1, 2, 3], 3, Found::At(Position(2))),
        (&[1, 2, 3], 9, Found::Absent),
    ];
    for subject in &SUBJECTS {
        let name = subject.name;
        // SAFETY: an empty range is read as no bytes.
        let empty = unsafe { (subject.find_byte)(NOWHERE, Byte(0)) };
        assert_eq!(Found::Absent, empty, "{name}");
        for (bytes, byte, found) in cases {
            // SAFETY: the range is a live array.
            let answer = unsafe { (subject.find_byte)(Range::from(bytes), Byte(byte)) };
            assert_eq!(found, answer, "{name}: {byte} in {bytes:?}");
        }
    }
}

/// Each function that reads a range reads no byte past a range that ends at
/// the end of a page, whose next page has no access: a read past it faults.
/// Each gives its answer over the three bytes `61 62 63` there.
#[test]
fn a_search_to_the_end_of_a_page_reads_no_byte_past_it()
{
    for subject in &SUBJECTS {
        let name = subject.name;
        let guarded = Guarded::new();
        let tail = Guarded::read(guarded.tail(Range::from(b"abc".as_slice())));
        // SAFETY: the range ends at the end of a readable page.
        let absent = unsafe { (subject.find_byte)(tail, Byte(b'z')) };
        // SAFETY: as above.
        let last = unsafe { (subject.find_byte)(tail, Byte(b'c')) };
        // SAFETY: as above, and the needle is a live array.
        let needle = unsafe { (subject.find_range)(tail, Range::from(b"c".as_slice())) };
        // SAFETY: as above.
        let past = unsafe { (subject.find_range)(tail, Range::from(b"bcd".as_slice())) };
        // SAFETY: as above.
        let utf8 = unsafe { (subject.check_utf8)(tail) };
        // SAFETY: as above.
        let zero = unsafe { (subject.find_zero)(tail) };
        // SAFETY: as above.
        let order = unsafe { (subject.compare)(tail, Range::from(b"abz".as_slice())) };
        let answers = (absent, last, needle, past, utf8, zero, order);
        assert_eq!(
            (
                Found::Absent,
                Found::At(Position(2)),
                Found::At(Position(2)),
                Found::Absent,
                Utf8::Valid,
                Found::Absent,
                Ordering::Less,
            ),
            answers,
            "{name}"
        );
    }
}

/// A range is found at its first whole match: an empty needle at 0, in an
/// empty range too; a needle of one byte; a needle that matches in part
/// before its whole match; a needle at the last position; and a needle
/// longer than the range, which is absent.
#[test]
fn a_range_is_found_at_its_first_whole_match()
{
    let cases: [(&[u8], &[u8], Found); 6] = [
        (b"abc", b"", Found::At(Position(0))),
        (b"abc", b"b", Found::At(Position(1))),
        (b"aaab", b"aab", Found::At(Position(1))),
        (b"abcab", b"ab", Found::At(Position(0))),
        (b"abcd", b"cd", Found::At(Position(2))),
        (b"ab", b"abc", Found::Absent),
    ];
    for subject in &SUBJECTS {
        let name = subject.name;
        // SAFETY: empty ranges are read as no bytes.
        let empty = unsafe { (subject.find_range)(NOWHERE, NOWHERE) };
        assert_eq!(Found::At(Position(0)), empty, "{name}: empty in empty");
        // SAFETY: as above, and the needle is a live array.
        let absent = unsafe { (subject.find_range)(NOWHERE, Range::from(b"a".as_slice())) };
        assert_eq!(Found::Absent, absent, "{name}: a byte in empty");
        for (bytes, needle, found) in cases {
            // SAFETY: both ranges are live arrays.
            let answer = unsafe { (subject.find_range)(Range::from(bytes), Range::from(needle)) };
            assert_eq!(found, answer, "{name}: {needle:?} in {bytes:?}");
        }
    }
}
