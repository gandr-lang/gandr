//! Boundary witnesses of the dyadic domain: the canonical form at the `i64`
//! edges, the precision range, exponent overflow, the far sum, and the order
//! and negation across the two carriers.

use core::cmp::Ordering;
use core::ops::Add as _;
use core::ops::Neg as _;
use core::ops::Shl as _;

use gandr_theory_exact_reals::BitWidth;
use gandr_theory_exact_reals::Dyadic;
use gandr_theory_exact_reals::DyadicError;
use gandr_theory_exact_reals::Exactness;
use gandr_theory_exact_reals::Exponent;
use gandr_theory_exact_reals::Precision;
use gandr_theory_exact_reals::Rounding;
use gandr_theory_exact_reals::Sign;
use num_bigint::BigInt;

/// The dyadic `mantissa · 2^exponent`.
///
/// # Specification
/// trivial.
fn dyadic(
    mantissa: BigInt,
    exponent: Exponent,
) -> Dyadic
{
    return Dyadic::new(mantissa, exponent).unwrap();
}

/// `2^bits + 1`, an odd integer just past a power of two.
///
/// # Specification
/// trivial.
fn past_power(bits: BitWidth) -> BigInt
{
    return BigInt::from(1_u8).shl(u64::from(bits)).add(1_u8);
}

#[test]
fn precision_admits_exactly_its_range()
{
    assert_eq!(
        Precision::try_from(0_u32),
        Err(DyadicError::PrecisionOutOfRange)
    );
    assert_eq!(Precision::try_from(1_u32), Ok(Precision::MIN));
    assert_eq!(
        Precision::try_from(u32::from(Precision::MAX)),
        Ok(Precision::MAX)
    );
    let past = u32::from(Precision::MAX).checked_add(1).unwrap();
    assert_eq!(
        Precision::try_from(past),
        Err(DyadicError::PrecisionOutOfRange)
    );
}

#[test]
fn errors_render_one_distinct_line()
{
    let lines = [
        DyadicError::ExponentOutOfRange,
        DyadicError::PrecisionOutOfRange,
    ]
    .map(|error| error.to_string());
    for line in &lines {
        assert!(
            !line.is_empty() && !line.contains('\n'),
            "not one line: {line}"
        );
    }
    assert_ne!(lines[0], lines[1]);
}

#[test]
fn new_strips_trailing_zeros_into_the_exponent()
{
    let value = dyadic(BigInt::from(12_u8), Exponent::from(0_i32));
    assert_eq!(value.mantissa(), BigInt::from(3_u8));
    assert_eq!(value.exponent(), Exponent::from(2_i32));
    let value = dyadic(BigInt::from(-8_i8), Exponent::from(5_i32));
    assert_eq!(value.mantissa(), BigInt::from(-1_i8));
    assert_eq!(value.exponent(), Exponent::from(8_i32));
    assert_eq!(dyadic(BigInt::ZERO, Exponent::from(7_i32)), Dyadic::ZERO);
    assert_eq!(Dyadic::ZERO.exponent(), Exponent::from(0_i32));
}

#[test]
fn new_keeps_the_i64_boundary_canonical()
{
    let zero = Exponent::from(0_i32);
    // `i64::MAX` is odd and inline; `i64::MIN` is a power of two.
    assert_eq!(dyadic(BigInt::from(i64::MAX), zero), Dyadic::from(i64::MAX));
    let minimum = dyadic(BigInt::from(i64::MIN), zero);
    assert_eq!(minimum.mantissa(), BigInt::from(-1_i8));
    assert_eq!(minimum.exponent(), Exponent::from(63_i32));
    assert_eq!(minimum, Dyadic::from(i64::MIN));
    // One past each bound is carried, and equal values built two ways are
    // equal and hash alike.
    let above = past_power(BitWidth::from(63_u64));
    let carried = dyadic(above.clone(), zero);
    assert_eq!(carried.width(), BitWidth::from(64_u64));
    let doubled = dyadic(above.clone().shl(1_u8), Exponent::from(-1_i32));
    assert_eq!(carried, doubled);
    let below = above.neg();
    assert_eq!(dyadic(below.clone(), zero).mantissa(), below);
}

#[test]
fn new_refuses_an_exponent_past_its_range()
{
    assert_eq!(
        Dyadic::new(BigInt::from(2_u8), Exponent::from(i32::MAX)),
        Err(DyadicError::ExponentOutOfRange)
    );
    assert!(Dyadic::new(BigInt::from(1_u8), Exponent::from(i32::MAX)).is_ok());
}

#[test]
fn width_counts_the_magnitude_bits()
{
    assert_eq!(Dyadic::ZERO.width(), BitWidth::from(0_u64));
    assert_eq!(Dyadic::ONE.width(), BitWidth::from(1_u64));
    assert_eq!(Dyadic::from(i64::MAX).width(), BitWidth::from(63_u64));
    assert_eq!(
        Dyadic::from(i64::MAX.checked_neg().unwrap()).width(),
        BitWidth::from(63_u64)
    );
    let carried = dyadic(past_power(BitWidth::from(64_u64)), Exponent::from(0_i32));
    assert_eq!(carried.width(), BitWidth::from(65_u64));
}

#[test]
fn sign_reads_both_carriers()
{
    assert_eq!(Dyadic::ZERO.sign(), Sign::Zero);
    assert_eq!(Dyadic::from(5_i64).sign(), Sign::Positive);
    assert_eq!(Dyadic::from(-5_i64).sign(), Sign::Negative);
    let carried = past_power(BitWidth::from(70_u64));
    assert_eq!(
        dyadic(carried.clone(), Exponent::from(0_i32)).sign(),
        Sign::Positive
    );
    assert_eq!(
        dyadic(carried.neg(), Exponent::from(0_i32)).sign(),
        Sign::Negative
    );
}

#[test]
fn integers_enter_in_canonical_form()
{
    assert_eq!(Dyadic::from(0_i64), Dyadic::ZERO);
    assert_eq!(Dyadic::from(1_i64), Dyadic::ONE);
    let twelve = Dyadic::from(12_i64);
    assert_eq!(
        (twelve.mantissa(), twelve.exponent()),
        (BigInt::from(3_u8), Exponent::from(2_i32))
    );
    let minimum = Dyadic::from(i64::MIN);
    assert_eq!(
        (minimum.mantissa(), minimum.exponent()),
        (BigInt::from(-1_i8), Exponent::from(63_i32))
    );
}

#[test]
fn round_refuses_an_exponent_past_its_range()
{
    // A ten-bit mantissa whose exponent is five below the maximum: keeping
    // two bits raises the exponent by eight.
    let value = dyadic(
        BigInt::from(0x201_u16),
        Exponent::from(i32::MAX.checked_sub(5).unwrap()),
    );
    let two = Precision::try_from(2_u32).unwrap();
    assert_eq!(
        value.round(two, Rounding::Floor),
        Err(DyadicError::ExponentOutOfRange)
    );
    let ten = Precision::try_from(10_u32).unwrap();
    assert_eq!(
        value.round(ten, Rounding::Floor).unwrap().exactness(),
        Exactness::Exact
    );
}

#[test]
fn product_refuses_an_exponent_past_its_range()
{
    let exact = Precision::MAX;
    let top = dyadic(BigInt::from(1_u8), Exponent::from(i32::MAX));
    let two = Dyadic::from(2_i64);
    assert_eq!(
        top.mul(&two, exact, Rounding::Floor),
        Err(DyadicError::ExponentOutOfRange)
    );
    let bottom = dyadic(BigInt::from(1_u8), Exponent::from(i32::MIN));
    let half = dyadic(BigInt::from(1_u8), Exponent::from(-1_i32));
    assert_eq!(
        bottom.mul(&half, exact, Rounding::Floor),
        Err(DyadicError::ExponentOutOfRange)
    );
    assert!(top.mul(&half, exact, Rounding::Floor).is_ok());
}

#[test]
fn far_sum_costs_no_wide_shift()
{
    // The two operands lie 2^31 bits apart. An aligned sum would shift by
    // 2^31 bits and allocate 256 MiB; the sticky operand keeps it to a few
    // words.
    let big = dyadic(BigInt::from(1_u8), Exponent::from(0x4000_0000_i32));
    let small = dyadic(BigInt::from(1_u8), Exponent::from(-0x4000_0000_i32));
    let eight = Precision::try_from(8_u32).unwrap();
    let mut sums = None;
    let counted = allocation_counter::measure(|| {
        sums = Some((
            big.add(&small, eight, Rounding::Floor),
            big.add(&small, eight, Rounding::Ceiling),
            big.sub(&small, eight, Rounding::Floor),
        ));
    });
    assert!(
        counted.bytes_total < 0x1000,
        "the far sums allocated {} bytes",
        counted.bytes_total
    );
    let (floor, ceiling, below) = sums.unwrap();
    let floor = floor.unwrap();
    assert_eq!(floor.value(), &big);
    assert_eq!(floor.exactness(), Exactness::Inexact);
    // The next point above `2^(2^30)` on the grid of eight bits.
    let next = dyadic(BigInt::from(0x81_u8), Exponent::from(0x3FFF_FFF9_i32));
    assert_eq!(ceiling.unwrap().value(), &next);
    // The point below it: the grid is one bit finer under the power of two.
    let previous = dyadic(BigInt::from(0xFF_u8), Exponent::from(0x3FFF_FFF8_i32));
    assert_eq!(below.unwrap().value(), &previous);
}

#[test]
fn order_crosses_the_carriers()
{
    let zero = Exponent::from(0_i32);
    let carried = dyadic(past_power(BitWidth::from(64_u64)), zero);
    // `2^64 + 2`, carried with one bit fewer and an exponent one higher:
    // the same top bit.
    let shifted = dyadic(past_power(BitWidth::from(63_u64)), Exponent::from(1_i32));
    assert_eq!(carried.cmp(&shifted), Ordering::Less);
    assert_eq!((&carried).neg().cmp(&(&shifted).neg()), Ordering::Greater);
    assert_eq!(carried.cmp(&Dyadic::from(i64::MAX)), Ordering::Greater);
    assert_eq!(
        (&carried).neg().cmp(&Dyadic::from(i64::MIN)),
        Ordering::Less
    );
    assert_eq!(Dyadic::from(-1_i64).cmp(&Dyadic::ZERO), Ordering::Less);
    assert_eq!(carried.cmp(&carried.clone()), Ordering::Equal);
}

#[test]
fn negation_keeps_the_carrier_class()
{
    assert_eq!((&Dyadic::ZERO).neg(), Dyadic::ZERO);
    assert_eq!((&Dyadic::from(5_i64)).neg(), Dyadic::from(-5_i64));
    let zero = Exponent::from(0_i32);
    let carried = past_power(BitWidth::from(63_u64));
    assert_eq!(
        (&dyadic(carried.clone(), zero)).neg(),
        dyadic(carried.neg(), zero)
    );
    assert_eq!(
        (&Dyadic::from(i64::MAX)).neg(),
        Dyadic::from(i64::MAX.checked_neg().unwrap())
    );
}
