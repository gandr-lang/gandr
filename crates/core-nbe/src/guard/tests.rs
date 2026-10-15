use alloc::string::String;
use core::hash::Hasher as _;

use anodized::spec;
use gandr_kernel_term::IntegerLiteral;
use gandr_kernel_term::Literal;
use gandr_kernel_term::Magnitude;
use gandr_kernel_term::Sign;

use super::ContentHash;
use super::FNV_OFFSET;
use super::Fold;
use super::Guard;
use super::GuardAnswer;
use super::GuardTag;

/// The non-negative integer literal spelled by `digits`.
///
/// # Specification
/// - requires: `digits` is a non-empty run of decimal digits.
/// - ensures: the integer literal those digits spell.
/// - provides: the payloads the folding witnesses compare.
/// - panics: when `digits` is not decimal, which no fixture passes.
///
/// # Adequacy
/// - hypothesis: L1 — the fixture spellings `1`, `2` and `0001` are observed
///   through equal-content hashing, distinct magnitudes and the opposite sign.
///   A constant payload, loss of canonical decimal identity or a negative
///   fixture changes an observation.
/// - witness: `guard::tests::equal_content_folds_to_one_word`
#[spec(requires: !digits.is_empty() && digits.bytes().all(|byte| byte.is_ascii_digit()))]
fn integer(digits: String) -> Literal
{
    let magnitude = Magnitude::from_decimal_text(digits).expect("the digits are decimal");
    Literal::Integer(IntegerLiteral::new(Sign::NonNegative, magnitude))
}

#[test]
fn equal_content_folds_to_one_word()
{
    let unit = Guard::compose(GuardTag::Tuple, &0_usize, &[]);
    let one = Guard::compose(GuardTag::Literal, &integer(String::from("1")), &[]);
    let first = Guard::compose(GuardTag::Tuple, &2_usize, &[unit, one]);
    let again = Guard::compose(GuardTag::Tuple, &2_usize, &[
        Guard::compose(GuardTag::Tuple, &0_usize, &[]),
        Guard::compose(GuardTag::Literal, &integer(String::from("1")), &[]),
    ]);
    assert_eq!(
        first, again,
        "equal content folds to one word wherever it is minted"
    );
    assert!(
        matches!(first, Guard::Rigid(_)),
        "and content with no closure inside is rigid"
    );
    let two = Guard::compose(GuardTag::Literal, &integer(String::from("2")), &[]);
    assert_ne!(
        first,
        Guard::compose(GuardTag::Tuple, &2_usize, &[unit, two]),
        "a differing payload folds apart"
    );
    assert_ne!(
        first,
        Guard::compose(GuardTag::Tuple, &2_usize, &[one, unit]),
        "and so does the same content in another order"
    );
    let padded = integer(String::from("0001"));
    assert_eq!(one, Guard::compose(GuardTag::Literal, &padded, &[]));
    let negative = Literal::Integer(IntegerLiteral::new(
        Sign::Negative,
        Magnitude::from_decimal_text(String::from("1")).expect("one is decimal"),
    ));
    assert_ne!(one, Guard::compose(GuardTag::Literal, &negative, &[]));
}

#[test]
fn a_flexible_child_makes_its_parent_flexible()
{
    let unit = Guard::compose(GuardTag::Tuple, &0_usize, &[]);
    for children in [[Guard::Flexible, unit], [unit, Guard::Flexible], [
        Guard::Flexible,
        Guard::Flexible,
    ]] {
        assert_eq!(
            Guard::Flexible,
            Guard::compose(GuardTag::Tuple, &2_usize, &children)
        );
    }
}

#[test]
fn only_two_rigid_words_that_differ_are_apart()
{
    let unit = Guard::compose(GuardTag::Tuple, &0_usize, &[]);
    let one = Guard::compose(GuardTag::Literal, &integer(String::from("1")), &[]);
    let words = [unit, one, Guard::Flexible];
    let expected = [
        [
            GuardAnswer::Inconclusive,
            GuardAnswer::Apart,
            GuardAnswer::Inconclusive,
        ],
        [
            GuardAnswer::Apart,
            GuardAnswer::Inconclusive,
            GuardAnswer::Inconclusive,
        ],
        [
            GuardAnswer::Inconclusive,
            GuardAnswer::Inconclusive,
            GuardAnswer::Inconclusive,
        ],
    ];
    for (left, row) in words.into_iter().zip(expected) {
        for (right, answer) in words.into_iter().zip(row) {
            assert_eq!(answer, left.settles(right));
        }
    }
}

#[test]
fn fnv_vectors_preserve_empty_and_segmented_writes()
{
    // Published FNV-1a vectors: https://github.com/ronshabi/fnv1a.
    for (bytes, expected) in [
        (b"".as_slice(), 0xcbf2_9ce4_8422_2325_u64),
        (b"a".as_slice(), 0xaf63_dc4c_8601_ec8c_u64),
        (b"foobar".as_slice(), 0x8594_4171_f739_67e8_u64),
    ] {
        let mut fold = Fold(FNV_OFFSET);
        fold.write(bytes);
        assert_eq!(expected, fold.finish());
    }
    let mut segmented = Fold(FNV_OFFSET);
    segmented.write(b"foo");
    segmented.write(b"");
    segmented.write(b"bar");
    assert_eq!(0x8594_4171_f739_67e8_u64, segmented.finish());
    assert_eq!(0xcbf2_9ce4_8422_2325_u64, u64::from(ContentHash::of(&())));
    assert_eq!(0xaf63_dc4c_8601_ec8c_u64, u64::from(ContentHash::of(&b'a')));
}
