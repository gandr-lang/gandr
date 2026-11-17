use alloc::vec::Vec;

use gandr_surface_corpus::Bits;

use super::Advanced;
use super::Declined;
use super::Drawn;
use super::Draws;
use super::WIDEST;
use super::Width;
use super::draw;

/// At each width from one to 64, a draw lies below `2^width`. At width one a
/// draw is zero or one, and at width 64 it is any word.
#[test]
fn a_draw_lies_below_two_to_its_width_at_each_width()
{
    for bits in 1 ..= WIDEST {
        let Drawn(drawn) = draw(Width(bits)).expect("the entropy source answers");
        assert_eq!(
            drawn.checked_shr(bits).unwrap_or(0),
            0,
            "a draw of {bits} bits lies below 2^{bits}: {drawn}"
        );
    }
}

/// 256 draws of two bits give each of the four values. The chance that a
/// fair source misses one of them is below `2^-100`.
#[test]
fn draws_of_two_bits_give_each_of_the_four_values()
{
    let mut seen = [false; 4];
    for _ in 0 .. 256_u16 {
        let Drawn(drawn) = draw(Width(2)).expect("the entropy source answers");
        let slot = usize::try_from(drawn).expect("a draw of two bits is below four");
        *seen
            .get_mut(slot)
            .expect("a draw of two bits is below four") = true;
    }
    assert_eq!(seen, [true; 4], "each value of two bits is drawn");
}

/// Two draws of two bits walk the 16 paths depth first, each once, in the
/// lexicographic order of their answers, and each path takes four bits.
#[test]
fn two_draws_of_two_bits_walk_sixteen_paths_in_order()
{
    let mut draws = Draws::new(Bits::QUOTA);
    let mut walked = Vec::new();
    loop {
        let Drawn(first) = draws
            .answer(Width(2))
            .expect("four bits lie within the quota");
        let Drawn(second) = draws
            .answer(Width(2))
            .expect("four bits lie within the quota");
        walked.push((first, second, u32::from(draws.bits())));
        if draws.advance() == Advanced::Done {
            break;
        }
    }
    let expected: Vec<(u64, u64, u32)> = (0 .. 4_u64)
        .flat_map(|first| (0 .. 4_u64).map(move |second| (first, second, 4)))
        .collect();
    assert_eq!(walked, expected, "the paths come depth first, each once");
}

/// A path whose second draw follows from its first answer: a first answer of
/// 0 draws two bits more and a first answer of 1 draws none. The walk takes
/// five paths, and the last one takes one bit.
#[test]
fn a_path_s_draws_follow_its_earlier_answers()
{
    let mut draws = Draws::new(Bits::QUOTA);
    let mut walked = Vec::new();
    loop {
        let Drawn(first) = draws
            .answer(Width(1))
            .expect("one bit lies within the quota");
        let second = (first == 0).then(|| draws.answer(Width(2)).map(|Drawn(second)| second));
        walked.push((first, second, u32::from(draws.bits())));
        if draws.advance() == Advanced::Done {
            break;
        }
    }
    assert_eq!(
        walked,
        [
            (0, Some(Ok(0)), 3),
            (0, Some(Ok(1)), 3),
            (0, Some(Ok(2)), 3),
            (0, Some(Ok(3)), 3),
            (1, None, 1),
        ],
        "each answer of the first draw opens its own subtree"
    );
}

/// A draw that takes the path past the quota of 16 bits is declined, and the
/// path is marked with the bits it would take.
#[test]
fn a_draw_past_the_quota_is_marked()
{
    let mut draws = Draws::new(Bits::QUOTA);
    assert_eq!(
        draws.answer(Width(16)),
        Ok(Drawn(0)),
        "16 bits lie within the quota"
    );
    assert_eq!(draws.past(), None, "no draw passed the quota yet");
    assert_eq!(
        draws.answer(Width(1)),
        Err(Declined::PastQuota(17)),
        "a seventeenth bit passes the quota"
    );
    assert_eq!(draws.past(), Some(Bits::from(17_u32)), "the path is marked");
}
