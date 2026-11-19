//! The small string: its three forms, the edge at 23 bytes, and the allocator
//! as its parameter.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    expect(
        primitive_signature,
        reason = "the fixture builds a text from its length and the width of its last character"
    )
)]

use alloc::alloc::Global;
use alloc::collections::BTreeSet;
use core::hash::BuildHasher as _;
use std::collections::HashSet;
use std::hash::RandomState;

use gandr_kernel_data::Budget;
use gandr_kernel_data::Emptiness;
use gandr_kernel_data::Fits;
use gandr_kernel_data::SmallString;
use gandr_kernel_data::Text;
use gandr_kernel_data::scoped;

/// The inline bytes of a small string.
const INLINE: usize = 23;

/// The bytes of a small string in the global allocator.
const WIDTH: usize = 24;

/// A budget of two chunks of a region's allocator face: room for a text and
/// its copy, and not for a text of the whole budget.
const TWO_CHUNKS: usize = 8_192;

/// A text of `length` bytes that ends on a character of `width` bytes, with
/// the bytes before it ASCII.
///
/// # Specification
/// trivial.
fn text(
    length: usize,
    width: usize,
) -> String
{
    let last = match width {
        1 => 'a',
        2 => 'é',
        3 => '€',
        _ => '😀',
    };
    let mut out = String::new();
    while out.len().saturating_add(last.len_utf8()) < length {
        out.push('b');
    }
    if out.len().saturating_add(last.len_utf8()) == length {
        out.push(last);
    }
    while out.len() < length {
        out.push('c');
    }
    out
}

/// Each length from 0 to 64 bytes, with a last character of 1 to 4 bytes,
/// reads back its text and its length, inline up to 23 bytes and in a block
/// past them; the empty string is empty and a string of one byte is not.
#[test]
fn each_length_reads_back_its_text_in_each_form()
{
    for width in 1 ..= 4 {
        for length in 0 ..= 64 {
            let source = text(length, width);
            let string = SmallString::from_in(Text::from(source.as_str()), Global)
                .expect("the global allocator holds the block");
            assert_eq!(&*string, source, "the text of {length} bytes reads back");
            assert_eq!(
                usize::from(string.len()),
                source.len(),
                "its length reads back"
            );
            let converted = SmallString::<Global>::try_from(source.as_str())
                .expect("the global allocator holds the block");
            assert_eq!(converted, string, "the conversion builds the same text");
        }
    }
    assert_eq!(
        SmallString::new().is_empty(),
        Emptiness::Empty,
        "the new string is empty"
    );
    let one = SmallString::<Global>::try_from("a").expect("one byte is inline");
    assert_eq!(
        one.is_empty(),
        Emptiness::Occupied,
        "a string of one byte is not empty"
    );
}

/// A push at each character boundary of each text up to 40 bytes reads back
/// the whole text, across the edge at 23 bytes in the two directions, and a
/// text pushed onto a block takes a longer block.
#[test]
fn push_str_crosses_the_inline_edge_at_each_split()
{
    for width in 1 ..= 4 {
        for length in 0 ..= 40 {
            let source = text(length, width);
            for split in (0 ..= source.len()).filter(|split| source.is_char_boundary(*split)) {
                let (head, tail) = source.split_at(split);
                let mut string = SmallString::<Global>::try_from(head)
                    .expect("the global allocator holds the block");
                string
                    .push_str(Text::from(tail))
                    .expect("the global allocator holds the block");
                assert_eq!(
                    &*string, source,
                    "the split at {split} of {length} bytes reads back"
                );
                string
                    .push_str(Text::from(head))
                    .expect("the global allocator holds the block");
                assert_eq!(
                    &*string,
                    format!("{source}{head}"),
                    "a second push reads back"
                );
            }
        }
    }
}

/// A static text reads back and spills to a block on a push.
#[test]
fn a_static_text_reads_back_and_spills_on_a_push()
{
    let long = "a static text that is longer than the inline bytes";
    let mut string = SmallString::from_static(Text::from(long));
    assert_eq!(&*string, long, "the static text reads back");
    let copy = string.clone();
    string
        .push_str(Text::from("!"))
        .expect("the global allocator holds the block");
    assert_eq!(
        &*string,
        format!("{long}!"),
        "the push spills the text to a block"
    );
    assert_eq!(&*copy, long, "a copy of the static text keeps it");
    let short = SmallString::from_static(Text::from("short"));
    assert_eq!(&*short, "short", "a short static text reads back");
}

/// A text of 23 bytes fits and builds inline with no refusal to answer, and a
/// text of 24 bytes does not fit.
#[test]
fn a_text_that_fits_builds_inline_and_a_longer_one_does_not_fit()
{
    let edge = text(INLINE, 3);
    let fits = Fits::new(Text::from(edge.as_str())).expect("23 bytes fit");
    let string = SmallString::<Global>::from(fits);
    assert_eq!(&*string, edge, "the text that fits reads back");
    let past = text(INLINE.saturating_add(1), 1);
    assert!(
        Fits::new(Text::from(past.as_str())).is_none(),
        "24 bytes do not fit"
    );
}

/// A long text lives in a region's bytes, and a copy of it too; a push past
/// the region's budget is refused, and the string keeps its text. A text of
/// 23 bytes takes no block, so a region of no budget holds it.
#[test]
fn a_string_in_a_region_lives_in_its_bytes_and_is_refused_past_its_budget()
{
    let (read, copied, refused, kept) =
        scoped::<u64, _, _>(Budget::from(TWO_CHUNKS), |region, _mint| {
            let long = text(40, 2);
            let mut string = SmallString::from_in(Text::from(long.as_str()), region)
                .expect("the region holds the block");
            let copy = string.try_clone().expect("the region holds the copy");
            let past = "x".repeat(TWO_CHUNKS);
            let refused = string.push_str(Text::from(past.as_str())).is_err();
            (
                *string == long,
                *copy == long,
                refused,
                string.len() == copy.len(),
            )
        });
    assert!(read, "the text in the region reads back");
    assert!(copied, "the copy in the region reads back");
    assert!(refused, "a push past the budget is refused");
    assert!(kept, "a refused push leaves the text as it was");
    let (edge, past) = scoped::<u64, _, _>(Budget::from(0), |region, _mint| {
        let edge = text(INLINE, 4);
        let past = text(INLINE.saturating_add(1), 1);
        (
            SmallString::from_in(Text::from(edge.as_str()), region)
                .is_ok_and(|string| *string == edge),
            SmallString::from_in(Text::from(past.as_str()), region).is_err(),
        )
    });
    assert!(
        edge,
        "a text of 23 bytes takes no block, so a region of no budget holds it"
    );
    assert!(
        past,
        "a text of 24 bytes takes a block, which a region of no budget refuses"
    );
}

/// The string and an `Option` of it are 24 bytes for the global allocator,
/// and the string compares, orders and hashes as its text, whatever form
/// holds it.
#[test]
fn the_string_is_24_bytes_and_compares_as_its_text()
{
    assert_eq!(
        core::mem::size_of::<SmallString<Global>>(),
        WIDTH,
        "the global allocator's string is 24 bytes"
    );
    assert_eq!(
        core::mem::size_of::<Option<SmallString<Global>>>(),
        WIDTH,
        "an option of a string keeps its tag in the string's niche"
    );
    let long = text(40, 1);
    let inline = SmallString::<Global>::try_from("name").expect("inline");
    let heap = SmallString::<Global>::try_from(long.as_str()).expect("a block");
    let fixed = SmallString::from_static(Text::from("name"));
    assert_eq!(
        inline, fixed,
        "an inline and a static text of one spelling are equal"
    );
    assert_eq!(inline.clone(), inline, "a copy is equal");
    assert_eq!(heap.clone(), heap, "a copy of a block is equal");
    let hasher = RandomState::new();
    assert_eq!(
        hasher.hash_one(&inline),
        hasher.hash_one("name"),
        "a string hashes as its text"
    );
    let set: HashSet<SmallString<Global>> = [inline, heap.clone()].into_iter().collect();
    let again = SmallString::<Global>::try_from(long.as_str()).expect("a block");
    assert!(
        set.contains(&fixed) && set.contains(&again),
        "a set finds a key by an equal string of another form"
    );
    let ordered: BTreeSet<SmallString<Global>> = [heap, fixed.clone()].into_iter().collect();
    let order: Vec<&str> = ordered.iter().map(|string| &**string).collect();
    let mut expected = vec![long.as_str(), "name"];
    expected.sort_unstable();
    assert_eq!(order, expected, "strings order as their texts");
    assert_eq!(format!("{fixed}"), "name", "a string displays as its text");
}

/// A text whose block is its exact length crosses both ways with the same
/// pointer and no new block. A short text takes the inline form. An inline
/// text takes one new block on the way back.
#[test]
fn a_text_in_a_block_crosses_with_no_copy()
{
    let mut exact = String::with_capacity(24);
    exact.push_str("0123456789abcdefghijklmn");
    assert_eq!(
        exact.capacity(),
        exact.len(),
        "the block is the text's length"
    );
    let pointer = exact.as_ptr();
    let small = SmallString::<Global>::from(exact);
    assert_eq!(&*small, "0123456789abcdefghijklmn");
    assert_eq!(small.as_ptr(), pointer, "the block keeps its pointer");
    let back = String::from(small);
    assert_eq!(back, "0123456789abcdefghijklmn");
    assert_eq!(back.as_ptr(), pointer, "the return keeps the pointer");

    let short = String::from("region");
    let inline = SmallString::<Global>::from(short);
    assert_eq!(&*inline, "region");
    let taken = String::from(inline);
    assert_eq!(taken, "region", "an inline text takes one block");

    let empty = SmallString::<Global>::from(String::new());
    assert_eq!(
        empty.is_empty(),
        Emptiness::Empty,
        "an empty text takes the inline form"
    );
    assert_eq!(String::from(empty), "");
}
