//! The string buffer against its contract: each append of valid UTF-8 stands
//! in order with one zero byte after it, bytes that are not UTF-8 are rejected
//! where they fail with the buffer unchanged, and a vector becomes a buffer
//! only when its bytes pass the check.

use gandr_boot_alloc::Heap;
use gandr_boot_core::Byte;
use gandr_boot_core::Length;
use gandr_boot_core::Position;
use gandr_boot_core::Range;
use gandr_boot_data::Rejected;
use gandr_boot_data::StringBuffer;
use gandr_boot_data::Vector;

use crate::host;

/// The bytes of `range`.
///
/// # Specification
/// trivial.
fn bytes(range: Range) -> Vec<u8>
{
    if range.length.0 == 0 {
        return Vec::new();
    }
    // SAFETY: each range of a test is the bytes of a live buffer or vector,
    // which no call writes while the copy is made.
    unsafe { core::slice::from_raw_parts(range.base, range.length.0) }.to_vec()
}

/// Appends `text` to `buffer`.
///
/// # Specification
/// trivial.
fn appended(
    buffer: &mut StringBuffer<'_>,
    text: &[u8],
) -> Result<(), Rejected>
{
    // SAFETY: the bytes of `text` are readable and are no byte of the buffer.
    unsafe { buffer.append(Range::from(text)) }
}

/// A buffer with no byte holds no block: its text is an empty range with a
/// null address, its bytes with the zero are one zero byte, and its release
/// asks the heap for nothing.
#[test]
fn an_empty_buffer_is_one_zero_byte()
{
    let heap = Heap::new(host::page());
    let buffer = StringBuffer::new(&heap);
    assert_eq!(buffer.length(), Length(0), "no byte stands");
    assert!(buffer.range().base.is_null(), "no block");
    assert_eq!(bytes(buffer.terminated()), [0], "one zero byte");
    assert_eq!(buffer.release(), Ok(()), "the release frees nothing");
}

/// Appends of sequences of one, two, three and four bytes stand in order
/// through a growth past one size class, and one zero byte follows the text
/// after each append. An empty append adds nothing.
#[test]
fn each_append_stands_in_order_with_a_zero_after_it()
{
    let heap = Heap::new(host::page());
    let mut buffer = StringBuffer::new(&heap);
    let pieces: [&[u8]; 4] = [
        b"a",
        "\u{e9}".as_bytes(),
        "\u{2713}".as_bytes(),
        "\u{1d11e}".as_bytes(),
    ];
    let mut expected = Vec::new();
    for round in 0 .. 500_usize {
        let piece = pieces[round % pieces.len()];
        appended(&mut buffer, piece).expect("valid UTF-8 is written");
        expected.extend_from_slice(piece);
        assert_eq!(buffer.length(), Length(expected.len()), "the text grows");
        let mut terminated = expected.clone();
        terminated.push(0);
        assert_eq!(
            bytes(buffer.terminated()),
            terminated,
            "a zero after the text"
        );
    }
    appended(&mut buffer, b"").expect("an empty append is written");
    assert_eq!(bytes(buffer.range()), expected, "the text in order");
    assert!(
        core::str::from_utf8(&bytes(buffer.range())).is_ok(),
        "the text is UTF-8"
    );
}

/// A byte that starts no sequence, a sequence of a surrogate, and a sequence
/// that the bytes cut at their end are each rejected at the position where
/// they fail. The buffer keeps its text and the zero after it.
#[test]
fn bytes_that_are_not_utf8_are_rejected_where_they_fail()
{
    let heap = Heap::new(host::page());
    let mut buffer = StringBuffer::new(&heap);
    appended(&mut buffer, "ab\u{e9}".as_bytes()).expect("valid UTF-8 is written");
    let before = bytes(buffer.terminated());
    for (text, at) in [
        (&b"xy\xffz"[..], 2_usize),
        (&b"\xed\xa0\x80"[..], 0),
        (&b"ok\xe2\x82"[..], 2),
    ] {
        assert_eq!(
            appended(&mut buffer, text),
            Err(Rejected::Utf8(Position(at))),
            "{text:?}"
        );
        assert_eq!(
            bytes(buffer.terminated()),
            before,
            "the buffer keeps its bytes"
        );
    }
    let mut empty = StringBuffer::new(&heap);
    assert_eq!(
        appended(&mut empty, b"\x80"),
        Err(Rejected::Utf8(Position(0))),
        "a continuation byte alone"
    );
    assert!(
        empty.range().base.is_null(),
        "a rejected first append takes no block"
    );
}

/// A vector of valid UTF-8 becomes a buffer with the same text and a zero
/// after it, and gives its bytes back as a vector at the same address. A
/// vector with a fault comes back with its bytes and the position of the
/// fault.
#[test]
fn a_vector_becomes_a_buffer_when_its_bytes_are_utf8()
{
    let heap = Heap::new(host::page());
    let text = "z\u{fc}rich \u{2713}".as_bytes();
    let mut vector = Vector::new(&heap);
    for &byte in text {
        vector.push(Byte(byte)).expect("the heap grants the block");
    }
    let buffer = StringBuffer::from_vector(vector).expect("the bytes are UTF-8");
    assert_eq!(bytes(buffer.range()), text, "the same text");
    assert_eq!(
        bytes(buffer.terminated()).last(),
        Some(&0),
        "a zero after it"
    );
    let address = buffer.range().base;
    let back = buffer.into_vector();
    assert_eq!(bytes(back.range()), text, "the bytes, with no zero");
    assert_eq!(back.range().base, address, "no copy");

    let mut faulty = Vector::new(&heap);
    for &byte in b"ab\xc3" {
        faulty.push(Byte(byte)).expect("the heap grants the block");
    }
    let unchecked = StringBuffer::from_vector(faulty).expect_err("a cut sequence");
    assert_eq!(
        unchecked.rejected,
        Rejected::Utf8(Position(2)),
        "the position of the fault"
    );
    assert_eq!(
        bytes(unchecked.vector.range()),
        b"ab\xc3",
        "the vector keeps its bytes"
    );
}
