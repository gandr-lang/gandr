//! The block operations against each subject: a copy, a move, a fill and a
//! comparison, each on an empty range, on one byte, and on a range that ends
//! at the end of a page.

use core::cmp::Ordering;

use gandr_boot_core::Byte;
use gandr_boot_core::Length;
use gandr_boot_core::Place;
use gandr_boot_core::Range;
use gandr_boot_core::Short;

use crate::harness::NOWHERE;
use crate::harness::NOWHERE_TO;
use crate::harness::SUBJECTS;
use crate::host::Guarded;
use crate::host::Held;

/// The place of `count` bytes of `buffer` from `start`.
///
/// # Specification
/// trivial.
fn within(
    buffer: Place,
    start: Length,
    count: Length,
) -> Place
{
    Place {
        base: buffer.base.wrapping_add(start.0),
        length: count,
    }
}

/// A copy writes the source into the start of the place and keeps each other
/// byte: from an empty range at the null address, from one byte, and into a
/// place that ends at the end of a page. A place one byte too short takes
/// `Short`, and no byte of it changes.
#[test]
fn a_copy_writes_the_source_and_keeps_the_rest()
{
    for subject in &SUBJECTS {
        let name = subject.name;
        let mut to = [9_u8, 9];
        // SAFETY: the place is a live array, and the source is empty.
        let copied = unsafe { (subject.copy)(Place::from(to.as_mut_slice()), NOWHERE) };
        assert_eq!((Ok(()), [9, 9]), (copied, to), "{name}: empty");
        // SAFETY: an empty place takes an empty source and writes nothing.
        let copied = unsafe { (subject.copy)(NOWHERE_TO, NOWHERE) };
        assert_eq!(Ok(()), copied, "{name}: nowhere");
        let mut to = [9_u8, 9, 9];
        // SAFETY: the two arrays are live, and they share no byte.
        let copied =
            unsafe { (subject.copy)(Place::from(to.as_mut_slice()), Range::from([7].as_slice())) };
        assert_eq!((Ok(()), [7, 9, 9]), (copied, to), "{name}: one byte");
        let mut to = [9_u8];
        // SAFETY: as above.
        let short = unsafe {
            (subject.copy)(
                Place::from(to.as_mut_slice()),
                Range::from([1, 2].as_slice()),
            )
        };
        assert_eq!((Err(Short), [9]), (short, to), "{name}: short");
        let guarded = Guarded::new();
        let tail = guarded.tail(Range::from([0; 5].as_slice()));
        // SAFETY: the place ends at the end of a readable page, and the source
        // is a live array.
        let copied = unsafe { (subject.copy)(tail, Range::from([1, 2, 3, 4, 5].as_slice())) };
        assert_eq!(
            (Ok(()), Held(vec![1, 2, 3, 4, 5])),
            (copied, Guarded::bytes(tail)),
            "{name}: into the end of a page"
        );
        let mut to = [0_u8; 5];
        // SAFETY: the source ends at the end of a readable page.
        let copied = unsafe { (subject.copy)(Place::from(to.as_mut_slice()), Guarded::read(tail)) };
        assert_eq!(
            (Ok(()), [1, 2, 3, 4, 5]),
            (copied, to),
            "{name}: from the end of a page"
        );
    }
}

/// A move over shared bytes gives the bytes of the source as they were before
/// the move, forward and backward within one buffer and within the last bytes
/// of a page. An empty move and a move of one byte change only what they
/// state. A place too short takes `Short`, and no byte changes.
#[test]
fn a_move_over_shared_bytes_gives_the_source_as_it_was()
{
    for subject in &SUBJECTS {
        let name = subject.name;
        let mut buffer = [1_u8, 2, 3, 4, 5, 6, 7, 8];
        let from = Guarded::read(within(
            Place::from(buffer.as_mut_slice()),
            Length(0),
            Length(6),
        ));
        let to = within(Place::from(buffer.as_mut_slice()), Length(2), Length(6));
        // SAFETY: both ranges lie in the live buffer.
        let moved = unsafe { (subject.move_bytes)(to, from) };
        assert_eq!(
            (Ok(()), [1, 2, 1, 2, 3, 4, 5, 6]),
            (moved, buffer),
            "{name}: forward"
        );
        let mut buffer = [1_u8, 2, 3, 4, 5, 6, 7, 8];
        let from = Guarded::read(within(
            Place::from(buffer.as_mut_slice()),
            Length(2),
            Length(6),
        ));
        let to = within(Place::from(buffer.as_mut_slice()), Length(0), Length(6));
        // SAFETY: as above.
        let moved = unsafe { (subject.move_bytes)(to, from) };
        assert_eq!(
            (Ok(()), [3, 4, 5, 6, 7, 8, 7, 8]),
            (moved, buffer),
            "{name}: backward"
        );
        let mut buffer = [1_u8, 2];
        let from = Guarded::read(within(
            Place::from(buffer.as_mut_slice()),
            Length(0),
            Length(1),
        ));
        let to = within(Place::from(buffer.as_mut_slice()), Length(1), Length(1));
        // SAFETY: as above.
        let moved = unsafe { (subject.move_bytes)(to, from) };
        assert_eq!((Ok(()), [1, 1]), (moved, buffer), "{name}: one byte");
        // SAFETY: an empty place takes an empty source and writes nothing.
        let moved = unsafe { (subject.move_bytes)(NOWHERE_TO, NOWHERE) };
        assert_eq!(Ok(()), moved, "{name}: nowhere");
        let mut buffer = [1_u8, 2, 3];
        let from = Guarded::read(within(
            Place::from(buffer.as_mut_slice()),
            Length(0),
            Length(3),
        ));
        let to = within(Place::from(buffer.as_mut_slice()), Length(1), Length(2));
        // SAFETY: as above.
        let short = unsafe { (subject.move_bytes)(to, from) };
        assert_eq!((Err(Short), [1, 2, 3]), (short, buffer), "{name}: short");
        let guarded = Guarded::new();
        let tail = guarded.tail(Range::from([1, 2, 3, 4].as_slice()));
        let from = Range {
            base: tail.base.cast_const(),
            length: Length(3),
        };
        let to = Place {
            base: tail.base.wrapping_add(1),
            length: Length(3),
        };
        // SAFETY: both ranges lie in the readable page, and `to` ends at its
        // end.
        let moved = unsafe { (subject.move_bytes)(to, from) };
        assert_eq!(
            (Ok(()), Held(vec![1, 1, 2, 3])),
            (moved, Guarded::bytes(tail)),
            "{name}: at the end of a page"
        );
    }
}

/// A fill writes its byte to each byte of the place and to no byte beside
/// it: an empty place at the null address, one byte, four bytes inside a
/// buffer, and a place that ends at the end of a page.
#[test]
fn a_fill_writes_each_byte_of_the_place_alone()
{
    for subject in &SUBJECTS {
        let name = subject.name;
        // SAFETY: an empty place writes nothing.
        unsafe {
            (subject.fill)(NOWHERE_TO, Byte(7));
        }
        let mut buffer = [0_u8; 6];
        let place = within(Place::from(buffer.as_mut_slice()), Length(1), Length(4));
        // SAFETY: the place lies in the live buffer.
        unsafe {
            (subject.fill)(place, Byte(7));
        }
        assert_eq!([0, 7, 7, 7, 7, 0], buffer, "{name}: four bytes");
        let mut buffer = [0_u8; 3];
        let place = within(Place::from(buffer.as_mut_slice()), Length(1), Length(1));
        // SAFETY: as above.
        unsafe {
            (subject.fill)(place, Byte(0xFF));
        }
        assert_eq!([0, 0xFF, 0], buffer, "{name}: one byte");
        let guarded = Guarded::new();
        let tail = guarded.tail(Range::from([0; 3].as_slice()));
        // SAFETY: the place ends at the end of a readable page.
        unsafe {
            (subject.fill)(tail, Byte(5));
        }
        assert_eq!(
            Held(vec![5, 5, 5]),
            Guarded::bytes(tail),
            "{name}: at the end of a page"
        );
    }
}

/// Two empty ranges compare equal at any address, the null address included,
/// and an empty range comes before one byte.
#[test]
fn an_empty_range_compares_equal_at_any_address()
{
    for subject in &SUBJECTS {
        let name = subject.name;
        let dangling = Range {
            base: core::ptr::dangling(),
            length: Length(0),
        };
        // SAFETY: empty ranges are read as no bytes.
        let empty = unsafe { (subject.compare)(NOWHERE, dangling) };
        // SAFETY: as above, and the one byte is a live array.
        let shorter = unsafe { (subject.compare)(NOWHERE, Range::from([0].as_slice())) };
        assert_eq!(
            (Ordering::Equal, Ordering::Less),
            (empty, shorter),
            "{name}"
        );
    }
}

/// A comparison orders by the first byte where two ranges differ, as unsigned
/// numbers, and by the length when one range is the start of the other. A
/// range that ends at the end of a page compares with no read past it.
#[test]
fn a_comparison_orders_by_the_first_unequal_byte()
{
    let cases: [(&[u8], &[u8], Ordering); 6] = [
        (&[1, 2, 3], &[1, 2, 4], Ordering::Less),
        (&[1, 2, 4], &[1, 2, 3], Ordering::Greater),
        (&[1, 2], &[1, 2, 3], Ordering::Less),
        (&[0x80], &[0x7F], Ordering::Greater),
        (&[5], &[5], Ordering::Equal),
        (&[1, 2, 3], &[1, 2, 3], Ordering::Equal),
    ];
    for subject in &SUBJECTS {
        let name = subject.name;
        for (left, right, order) in cases {
            // SAFETY: both ranges are live arrays.
            let compared = unsafe { (subject.compare)(Range::from(left), Range::from(right)) };
            assert_eq!(order, compared, "{name}: {left:?} and {right:?}");
        }
        let guarded = Guarded::new();
        let tail = Guarded::read(guarded.tail(Range::from([5, 6, 7].as_slice())));
        // SAFETY: the range ends at the end of a readable page.
        let same = unsafe { (subject.compare)(tail, Range::from([5, 6, 7].as_slice())) };
        // SAFETY: as above.
        let longer = unsafe { (subject.compare)(tail, Range::from([5, 6, 7, 0].as_slice())) };
        assert_eq!((Ordering::Equal, Ordering::Less), (same, longer), "{name}");
    }
}
