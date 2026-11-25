//! The vector against its contract: each pushed byte stands in order through
//! each growth, a room within the capacity keeps the block, and a growth that
//! cannot be made leaves the vector as it was.

use gandr_boot_alloc::Heap;
use gandr_boot_core::Byte;
use gandr_boot_core::Length;
use gandr_boot_core::Position;
use gandr_boot_core::Range;
use gandr_boot_data::Refusal;
use gandr_boot_data::Vector;

use crate::host;

/// The byte at position `at` of the pattern of the tests: no run of equal
/// bytes, so a byte at a wrong position shows.
///
/// # Specification
/// trivial.
fn pattern(at: usize) -> u8
{
    u8::try_from(at.wrapping_mul(31).wrapping_add(at >> 8_u32) & 0xFF).expect("a byte")
}

/// The bytes that stand in `vector`.
///
/// # Specification
/// trivial.
fn standing<'vector>(vector: &'vector Vector<'_>) -> &'vector [u8]
{
    let range = vector.range();
    if range.length.0 == 0 {
        return &[];
    }
    // SAFETY: the range is the bytes that stand, and the vector is lent
    // shared while the slice lives.
    unsafe { core::slice::from_raw_parts(range.base, range.length.0) }
}

/// A vector with no byte holds no block: its length and its capacity are
/// zero, its range is empty with a null address, a read at position 0 gives
/// an absence, and its release asks the heap for nothing.
#[test]
fn an_empty_vector_holds_no_block()
{
    let heap = Heap::new(host::page());
    let vector = Vector::new(&heap);
    assert_eq!(vector.length(), Length(0), "no byte stands");
    assert_eq!(vector.capacity(), Length(0), "no block");
    assert!(
        vector.range().base.is_null(),
        "the empty range has no address"
    );
    assert_eq!(vector.range().length, Length(0), "the empty range");
    assert_eq!(vector.byte(Position(0)), None, "no byte at 0");
    assert_eq!(vector.release(), Ok(()), "the release frees nothing");
}

/// 100,000 pushed bytes stand in order, through each size class of the heap
/// and whole pages. The capacity is never less than the length, the last
/// byte reads back, and the position of the length gives an absence.
#[test]
fn each_pushed_byte_stands_in_order()
{
    let heap = Heap::new(host::page());
    let mut vector = Vector::new(&heap);
    for at in 0 .. 100_000_usize {
        vector
            .push(Byte(pattern(at)))
            .expect("the heap grants the block");
        assert!(
            vector.capacity() >= vector.length(),
            "the capacity holds the length at {at}"
        );
    }
    assert_eq!(vector.length(), Length(100_000), "each push stands");
    let expected = (0 .. 100_000_usize).map(pattern).collect::<Vec<_>>();
    assert_eq!(standing(&vector), expected.as_slice(), "the bytes in order");
    assert_eq!(
        vector.byte(Position(99_999)),
        Some(Byte(pattern(99_999))),
        "the last byte"
    );
    assert_eq!(
        vector.byte(Position(100_000)),
        None,
        "no byte at the length"
    );
}

/// A room within the capacity keeps the address of the block and the
/// capacity, and the pushes that fill it keep the address too.
#[test]
fn a_room_within_the_capacity_keeps_the_block()
{
    let heap = Heap::new(host::page());
    let mut vector = Vector::new(&heap);
    vector
        .reserve(Length(100))
        .expect("the heap grants the block");
    let capacity = vector.capacity();
    assert!(capacity >= Length(100), "the room is made");
    vector.push(Byte(1)).expect("the room holds one byte");
    let base = vector.range().base;
    vector
        .reserve(Length(capacity.0 - 1))
        .expect("the room stands");
    assert_eq!(vector.capacity(), capacity, "no growth");
    for at in 1 .. capacity.0 {
        vector
            .push(Byte(pattern(at)))
            .expect("the room holds the byte");
    }
    assert_eq!(vector.range().base, base, "the block stays");
    assert_eq!(vector.length(), capacity, "the block is full");
}

/// A room past the size of a layout is refused as `Size`, and a room whose
/// count overflows a word too. The vector keeps its bytes, its length and its
/// capacity.
#[test]
fn a_room_past_a_layout_is_refused()
{
    let heap = Heap::new(host::page());
    let mut vector = Vector::new(&heap);
    for at in 0 .. 40_usize {
        vector
            .push(Byte(pattern(at)))
            .expect("the heap grants the block");
    }
    let capacity = vector.capacity();
    let past = usize::try_from(isize::MAX).expect("a word") - 39;
    assert_eq!(
        vector.reserve(Length(past)),
        Err(Refusal::Size),
        "more than a layout holds"
    );
    assert_eq!(
        vector.reserve(Length(usize::MAX)),
        Err(Refusal::Size),
        "a count past a word"
    );
    assert_eq!(vector.capacity(), capacity, "the capacity stays");
    assert_eq!(vector.length(), Length(40), "the length stays");
    let expected = (0 .. 40_usize).map(pattern).collect::<Vec<_>>();
    assert_eq!(standing(&vector), expected.as_slice(), "the bytes stay");
}

/// An append after pushed bytes keeps them and adds its own in order, past
/// the size of one class. An empty range with a null address adds nothing.
#[test]
fn an_append_keeps_the_bytes_before_it()
{
    let heap = Heap::new(host::page());
    let mut vector = Vector::new(&heap);
    for at in 0 .. 10_usize {
        vector
            .push(Byte(pattern(at)))
            .expect("the heap grants the block");
    }
    let tail = (10 .. 5_000_usize).map(pattern).collect::<Vec<_>>();
    // SAFETY: the bytes of `tail` are readable and are no byte of the vector.
    unsafe { vector.append(Range::from(tail.as_slice())) }.expect("the heap grants the block");
    let empty = Range {
        base: core::ptr::null(),
        length: Length(0),
    };
    // SAFETY: the range is empty, so no byte of it is read.
    unsafe { vector.append(empty) }.expect("an empty range adds nothing");
    let expected = (0 .. 5_000_usize).map(pattern).collect::<Vec<_>>();
    assert_eq!(standing(&vector), expected.as_slice(), "the bytes in order");
}

/// A cut keeps the first bytes and the capacity, a cut past the length
/// changes nothing, and a push after a cut writes at the new length.
#[test]
fn a_cut_keeps_the_first_bytes()
{
    let heap = Heap::new(host::page());
    let mut vector = Vector::new(&heap);
    for at in 0 .. 50_usize {
        vector
            .push(Byte(pattern(at)))
            .expect("the heap grants the block");
    }
    let capacity = vector.capacity();
    vector.truncate(Length(80));
    assert_eq!(vector.length(), Length(50), "a cut past the length");
    vector.truncate(Length(20));
    assert_eq!(vector.length(), Length(20), "the cut");
    assert_eq!(vector.capacity(), capacity, "the capacity stays");
    vector.push(Byte(0xEE)).expect("the room holds the byte");
    let mut expected = (0 .. 20_usize).map(pattern).collect::<Vec<_>>();
    expected.push(0xEE);
    assert_eq!(standing(&vector), expected.as_slice(), "the first bytes");
}

/// The release of a vector of whole pages gives no refusal, and a vector of
/// a size class taken after it from the same heap reads its own bytes.
#[test]
fn a_release_gives_the_block_back()
{
    let heap = Heap::new(host::page());
    let mut pages = Vector::new(&heap);
    pages
        .reserve(Length(64 * 1024))
        .expect("the heap grants the pages");
    pages.push(Byte(7)).expect("the room holds the byte");
    assert_eq!(pages.release(), Ok(()), "the pages go back to the host");
    let mut small = Vector::new(&heap);
    small.push(Byte(9)).expect("the heap grants the block");
    assert_eq!(standing(&small), &[9_u8], "the byte of the new vector");
}
