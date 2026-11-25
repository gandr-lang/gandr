//! The one harness: each test runs its cases against each subject of
//! [`SUBJECTS`]. The crate is the one subject now. Its twin in gandr joins
//! as a second subject, so each case states one answer for both.

use core::cmp::Ordering;

use gandr_boot_core::Byte;
use gandr_boot_core::Found;
use gandr_boot_core::Place;
use gandr_boot_core::Range;
use gandr_boot_core::Short;
use gandr_boot_core::Utf8;

/// The operations of one subject, each with the signature of the crate's
/// function.
///
/// # Specification
/// trivial.
pub struct Subject
{
    /// The subject's name, which each failed case states.
    pub name: &'static str,
    /// The copy between two ranges that share no byte.
    pub copy: unsafe fn(Place, Range) -> Result<(), Short>,
    /// The move between two ranges that can share bytes.
    pub move_bytes: unsafe fn(Place, Range) -> Result<(), Short>,
    /// The fill.
    pub fill: unsafe fn(Place, Byte),
    /// The comparison.
    pub compare: unsafe fn(Range, Range) -> Ordering,
    /// The search of a byte.
    pub find_byte: unsafe fn(Range, Byte) -> Found,
    /// The search of a range.
    pub find_range: unsafe fn(Range, Range) -> Found,
    /// The check of UTF-8.
    pub check_utf8: unsafe fn(Range) -> Utf8,
    /// The search of a zero byte.
    pub find_zero: unsafe fn(Range) -> Found,
}

/// The subjects that each test runs against.
pub const SUBJECTS: [Subject; 1] = [Subject {
    name: "gandr-boot-core",
    copy: gandr_boot_core::copy,
    move_bytes: gandr_boot_core::move_bytes,
    fill: gandr_boot_core::fill,
    compare: gandr_boot_core::compare,
    find_byte: gandr_boot_core::find_byte,
    find_range: gandr_boot_core::find_range,
    check_utf8: gandr_boot_core::check_utf8,
    find_zero: gandr_boot_core::find_zero,
}];

/// An empty range at the null address, which no function may read.
pub const NOWHERE: Range = Range {
    base: core::ptr::null(),
    length: gandr_boot_core::Length(0),
};

/// An empty place at the null address, which no function may write.
pub const NOWHERE_TO: Place = Place {
    base: core::ptr::null_mut(),
    length: gandr_boot_core::Length(0),
};
