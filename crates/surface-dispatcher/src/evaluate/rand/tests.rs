use super::Drawn;
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
