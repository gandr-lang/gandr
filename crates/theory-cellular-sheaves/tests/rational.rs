//! The rationals as a caller builds them: each spelling of a number gives one
//! value in lowest terms, the refusals at the edges of the 128-bit integers,
//! and the exact sum, product and quotient.

use gandr_theory_cellular_sheaves::Integer;
use gandr_theory_cellular_sheaves::Rational;
use gandr_theory_cellular_sheaves::SheafError;

/// Each spelling of a number, by a common factor or by the sign on its
/// denominator, gives one value: the lowest terms with a positive
/// denominator.
#[test]
fn each_spelling_of_a_number_gives_its_lowest_terms()
{
    for (numerator, denominator, lowest) in [
        (6_i128, 4_i128, (3_i128, 2_i128)),
        (6, -4, (-3, 2)),
        (-6, -4, (3, 2)),
        (0, -5, (0, 1)),
        (7, 1, (7, 1)),
        (i128::MAX, i128::MAX, (1, 1)),
    ] {
        let value = rational!(numerator, denominator);
        assert_eq!(
            (
                i128::from(value.numerator()),
                i128::from(value.denominator())
            ),
            lowest,
            "{numerator}/{denominator}"
        );
    }
    assert_eq!(rational!(0, 9), Rational::ZERO);
    assert_eq!(rational!(-4, -4), Rational::ONE);
    assert_eq!(rational!(3, -6).to_string(), "-1/2");
    assert_eq!(rational!(8, 4).to_string(), "2");
}

/// A zero denominator is refused, and so is a part whose sign the integers
/// cannot move: the least 128-bit integer.
#[test]
fn a_zero_denominator_and_the_least_integer_are_refused()
{
    for (numerator, denominator) in [(1_i128, 0_i128), (i128::MIN, -1), (1, i128::MIN)] {
        assert_eq!(
            Rational::new(Integer::from(numerator), Integer::from(denominator)),
            Err(SheafError::Overflow),
            "{numerator}/{denominator}"
        );
    }
}

/// The sum, the product and the quotient are exact and in lowest terms, and
/// one past the integers, or a quotient by zero, is refused.
#[test]
fn the_arithmetic_is_exact_and_refuses_past_the_integers()
{
    assert_eq!(rational!(1, 2).plus(rational!(1, 3)), Ok(rational!(5, 6)));
    assert_eq!(rational!(1, 4).plus(rational!(3, 4)), Ok(Rational::ONE));
    assert_eq!(rational!(2, 3).times(rational!(3, 4)), Ok(rational!(1, 2)));
    assert_eq!(rational!(1, 2).over(rational!(1, 4)), Ok(rational!(2, 1)));
    assert_eq!(
        rational!(1, 2).over(Rational::ZERO),
        Err(SheafError::Overflow)
    );
    assert_eq!(
        rational!(i128::MAX, 1).times(rational!(2, 1)),
        Err(SheafError::Overflow)
    );
    assert_eq!(
        rational!(1, i128::MAX).plus(rational!(1, 2)),
        Err(SheafError::Overflow)
    );
}

/// A sum, a product or a quotient whose lowest terms lie in the integers is
/// given, even when the plain cross-multiplication of its operands passes
/// them: two weights over `2^64` sum to one, and the factors of `2^100` and
/// of `2^120` cancel before they multiply.
#[test]
fn a_result_in_range_is_given_whatever_its_operands()
{
    let two_to_the_64 = 0x0001_0000_0000_0000_0000_i128;
    let two_to_the_100 = 0x0010_0000_0000_0000_0000_0000_0000_i128;
    let two_to_the_120 = 0x0100_0000_0000_0000_0000_0000_0000_0000_i128;
    let below_one = two_to_the_64.checked_sub(1).expect("in range");
    assert_eq!(
        rational!(1, two_to_the_64).plus(rational!(below_one, two_to_the_64)),
        Ok(Rational::ONE)
    );
    assert_eq!(
        rational!(two_to_the_100, 3).times(rational!(0x3000_0000, two_to_the_100)),
        Ok(rational!(0x1000_0000, 1))
    );
    assert_eq!(
        rational!(two_to_the_120, 3).over(rational!(two_to_the_120, 7)),
        Ok(rational!(7, 3))
    );
}

/// The order of rationals is the order of the numbers, for each pair of signs
/// and for two spellings of one number. `(n + 1) / n` and `n / (n - 1)` near
/// the greatest integer have cross products past the integers, and the first
/// still lies below the second.
#[test]
fn the_order_of_rationals_is_the_order_of_the_numbers()
{
    use core::cmp::Ordering;

    let greatest = i128::MAX;
    let below = greatest - 1;
    for (left, right, order) in [
        (rational!(1, 3), rational!(1, 2), Ordering::Less),
        (rational!(-1, 2), rational!(1, 3), Ordering::Less),
        (rational!(-1, 3), rational!(-1, 2), Ordering::Greater),
        (rational!(2, 4), rational!(1, 2), Ordering::Equal),
        (rational!(7, 2), rational!(10, 3), Ordering::Greater),
        (Rational::ZERO, rational!(-1, greatest), Ordering::Greater),
        (
            rational!(greatest, below),
            rational!(below, below - 1),
            Ordering::Less,
        ),
    ] {
        assert_eq!(left.cmp(&right), order, "{left} against {right}");
        assert_eq!(right.cmp(&left), order.reverse(), "{right} against {left}");
    }
}
