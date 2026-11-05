//! The exemplar: a differential test of every dyadic and interval operation
//! against a slow exact-rational oracle.
//!
//! The oracle holds a value as a reduced fraction of two integers on the
//! carrier. It adds, subtracts and multiplies by cross multiplication, and it
//! compares by cross multiplication. It rounds a value to `p` significant
//! bits by finding the power of two `2^k` above the value and taking the
//! floor or the ceiling of the value over `2^(k - p)`. It shares no code with
//! the crate: no alignment, no inline path, no sticky operand and no sign
//! table. A mutant that moves the sticky position, swaps a rounding
//! direction, pairs the wrong interval endpoints or misreads a closure
//! disagrees with it on generated operands.

use core::cmp::Ordering;
use core::ops::Add as _;
use core::ops::Div as _;
use core::ops::Mul as _;
use core::ops::Neg as _;
use core::ops::Rem as _;
use core::ops::Shl as _;
use core::ops::Sub as _;

use anodized::spec;
use gandr_theory_exact_reals::Bound;
use gandr_theory_exact_reals::Closure;
use gandr_theory_exact_reals::Containment;
use gandr_theory_exact_reals::Dyadic;
use gandr_theory_exact_reals::Endpoint;
use gandr_theory_exact_reals::Exactness;
use gandr_theory_exact_reals::Exponent;
use gandr_theory_exact_reals::NumericInterval;
use gandr_theory_exact_reals::Orientation;
use gandr_theory_exact_reals::Precision;
use gandr_theory_exact_reals::Rounding;
use num_bigint::BigInt;
use proptest::prelude::ProptestConfig;
use proptest::prelude::Strategy;
use proptest::prelude::any;
use proptest::prop_assert_eq;
use proptest::prop_oneof;
use proptest::proptest;
use proptest::strategy::Just;

/// An exact rational: the denominator positive, the pair reduced.
#[derive(Clone, Debug, Eq, PartialEq)]
struct Rational
{
    /// The numerator.
    numerator: BigInt,
    /// The positive denominator.
    denominator: BigInt,
}

impl Rational
{
    /// The reduced fraction `numerator / denominator`.
    ///
    /// # Specification
    /// - requires: `denominator` is nonzero.
    /// - ensures: the result has a positive denominator and no common factor.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every oracle value passes through it.
    /// - witness: `tests::oracle::canonical_form_denotes_its_parts`
    #[spec(requires: denominator != BigInt::ZERO, ensures: |ref result| result.denominator > BigInt::ZERO)]
    fn reduced(
        numerator: BigInt,
        denominator: BigInt,
    ) -> Self
    {
        let (numerator, denominator) = if denominator < BigInt::ZERO {
            (numerator.neg(), denominator.neg())
        }
        else {
            (numerator, denominator)
        };
        let mut left = if numerator < BigInt::ZERO {
            numerator.clone().neg()
        }
        else {
            numerator.clone()
        };
        let mut right = denominator.clone();
        while right != BigInt::ZERO {
            let remainder = (&left).rem(&right);
            left = right;
            right = remainder;
        }
        if left == BigInt::ZERO {
            return Self {
                numerator: BigInt::ZERO,
                denominator: BigInt::from(1_u8),
            };
        }
        return Self {
            numerator: numerator.div(&left),
            denominator: denominator.div(&left),
        };
    }

    /// The rational a dyadic denotes, read through its parts.
    ///
    /// # Specification
    /// trivial.
    fn of(value: &Dyadic) -> Self
    {
        return Self::scaled(value.mantissa(), value.exponent());
    }

    /// The rational `mantissa · 2^exponent`.
    ///
    /// # Specification
    /// trivial.
    fn scaled(
        mantissa: BigInt,
        exponent: Exponent,
    ) -> Self
    {
        let exponent = i32::from(exponent);
        let shift = u64::from(exponent.unsigned_abs());
        if exponent >= 0_i32 {
            return Self::reduced(mantissa.shl(shift), BigInt::from(1_u8));
        }
        return Self::reduced(mantissa, BigInt::from(1_u8).shl(shift));
    }

    /// The exact sum.
    ///
    /// # Specification
    /// trivial.
    fn plus(
        &self,
        other: &Self,
    ) -> Self
    {
        let numerator = (&self.numerator)
            .mul(&other.denominator)
            .add((&other.numerator).mul(&self.denominator));
        return Self::reduced(numerator, (&self.denominator).mul(&other.denominator));
    }

    /// The exact difference.
    ///
    /// # Specification
    /// trivial.
    fn minus(
        &self,
        other: &Self,
    ) -> Self
    {
        let numerator = (&self.numerator)
            .mul(&other.denominator)
            .sub((&other.numerator).mul(&self.denominator));
        return Self::reduced(numerator, (&self.denominator).mul(&other.denominator));
    }

    /// The exact product.
    ///
    /// # Specification
    /// trivial.
    fn times(
        &self,
        other: &Self,
    ) -> Self
    {
        return Self::reduced(
            (&self.numerator).mul(&other.numerator),
            (&self.denominator).mul(&other.denominator),
        );
    }

    /// The exact order, by cross multiplication.
    ///
    /// # Specification
    /// trivial.
    fn order(
        &self,
        other: &Self,
    ) -> Ordering
    {
        return (&self.numerator)
            .mul(&other.denominator)
            .cmp(&(&other.numerator).mul(&self.denominator));
    }

    /// The floor or the ceiling of the value on the grid of `precision`
    /// significant bits.
    ///
    /// # Specification
    /// - ensures: zero rounds to zero; otherwise, with `2^(k - 1) <= |r| <
    ///   2^k`, returns `floor(r / 2^(k - p)) · 2^(k - p)` or the ceiling, a
    ///   reduced fraction. The executable clause checks the reduced form of the
    ///   result only, because a clause that reads the receiver walks its
    ///   digits.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the oracle's own rounding, independent of the crate's
    ///   shift and sticky paths.
    /// - witness: `tests::oracle::round_is_the_directed_neighbour_on_the_grid`
    #[spec(ensures: |ref result| result.denominator > BigInt::ZERO)]
    fn rounded(
        &self,
        precision: Precision,
        rounding: Rounding,
    ) -> Self
    {
        if self.numerator == BigInt::ZERO {
            return self.clone();
        }
        let magnitude = if self.numerator < BigInt::ZERO {
            self.numerator.clone().neg()
        }
        else {
            self.numerator.clone()
        };
        let numerator_bits = i64::try_from(magnitude.bits()).unwrap();
        let denominator_bits = i64::try_from(self.denominator.bits()).unwrap();
        let guess = numerator_bits.checked_sub(denominator_bits).unwrap();
        let power = |exponent: i64| {
            Self::scaled(
                BigInt::from(1_u8),
                Exponent::from(i32::try_from(exponent).unwrap()),
            )
        };
        // `|r| >= 2^guess` decides between `k = guess` and `k = guess + 1`.
        let at_least = Self::reduced(magnitude, self.denominator.clone()).order(&power(guess))
            != Ordering::Less;
        let top = if at_least {
            guess.checked_add(1).unwrap()
        }
        else {
            guess
        };
        let step = top.checked_sub(i64::from(u32::from(precision))).unwrap();
        let quotient = self.times(&power(step.checked_neg().unwrap()));
        let floor = floor_div(&quotient.numerator, &quotient.denominator);
        let grid = match rounding {
            Rounding::Floor => floor,
            Rounding::Ceiling => {
                if (&floor).mul(&quotient.denominator) == quotient.numerator {
                    floor
                }
                else {
                    floor.add(1_i64)
                }
            },
        };
        return Self::reduced(grid, BigInt::from(1_u8)).times(&power(step));
    }
}

/// The floor of `numerator / denominator` for a positive denominator.
///
/// # Specification
/// - requires: `denominator` is positive.
/// - ensures: returns `q` with `q · denominator <= numerator < (q + 1) ·
///   denominator`.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — through the oracle's rounding of negative values.
/// - witness: `tests::oracle::round_is_the_directed_neighbour_on_the_grid`
#[spec(requires: *denominator > BigInt::ZERO)]
fn floor_div(
    numerator: &BigInt,
    denominator: &BigInt,
) -> BigInt
{
    let quotient = numerator.div(denominator);
    let remainder = numerator.rem(denominator);
    if remainder < BigInt::ZERO {
        return quotient.sub(1_i64);
    }
    return quotient;
}

/// An exact value on the extended line.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Extended
{
    /// The negative infinity.
    NegInf,
    /// A rational.
    Finite(Rational),
    /// The positive infinity.
    PosInf,
}

impl Extended
{
    /// The extended value of an endpoint.
    ///
    /// # Specification
    /// trivial.
    fn of(endpoint: &Endpoint) -> Self
    {
        return match *endpoint {
            Endpoint::NegInf => Self::NegInf,
            Endpoint::Finite(ref value) => Self::Finite(Rational::of(value)),
            Endpoint::PosInf => Self::PosInf,
        };
    }

    /// The product, zero times an infinity being zero.
    ///
    /// # Specification
    /// trivial.
    fn times(
        &self,
        other: &Self,
    ) -> Self
    {
        let sign = |value: &Self| match *value {
            Self::NegInf => Ordering::Less,
            Self::Finite(ref rational) => rational.numerator.cmp(&BigInt::ZERO),
            Self::PosInf => Ordering::Greater,
        };
        return match (self, other) {
            (&Self::Finite(ref left), &Self::Finite(ref right)) => Self::Finite(left.times(right)),
            _ if sign(self) == Ordering::Equal || sign(other) == Ordering::Equal => {
                Self::Finite(Rational::reduced(BigInt::ZERO, BigInt::from(1_u8)))
            },
            _ if sign(self) == sign(other) => Self::PosInf,
            _ => Self::NegInf,
        };
    }

    /// The order on the extended line.
    ///
    /// # Specification
    /// trivial.
    fn order(
        &self,
        other: &Self,
    ) -> Ordering
    {
        return match (self, other) {
            (&Self::Finite(ref left), &Self::Finite(ref right)) => left.order(right),
            (&Self::NegInf, &Self::NegInf) | (&Self::PosInf, &Self::PosInf) => Ordering::Equal,
            (&Self::NegInf, _) | (_, &Self::PosInf) => Ordering::Less,
            (_, &Self::NegInf) | (&Self::PosInf, _) => Ordering::Greater,
        };
    }
}

/// The bound the oracle expects for an exact endpoint value that some pair
/// attains or not, rounded toward `rounding`.
///
/// # Specification
/// - ensures: an infinity is an open infinite bound; a finite value is its
///   oracle rounding, closed exactly when attained and exactly representable.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the expected bound of every interval operation.
/// - witness: `tests::oracle::interval_sum_and_difference_round_outward`
#[spec(ensures: |ref result| result.0 == Closure::Open || matches!(result.1, Extended::Finite(_)))]
fn expected(
    exact: &Extended,
    attained: Closure,
    precision: Precision,
    rounding: Rounding,
) -> (Closure, Extended)
{
    return match *exact {
        Extended::NegInf => (Closure::Open, Extended::NegInf),
        Extended::PosInf => (Closure::Open, Extended::PosInf),
        Extended::Finite(ref value) => {
            let rounded = value.rounded(precision, rounding);
            let closure = if attained == Closure::Closed && rounded == *value {
                Closure::Closed
            }
            else {
                Closure::Open
            };
            (closure, Extended::Finite(rounded))
        },
    };
}

/// A bound as the oracle reads it.
///
/// # Specification
/// trivial.
fn observed(bound: &Bound) -> (Closure, Extended)
{
    return (bound.closure, Extended::of(&bound.endpoint));
}

/// Generated dyadics: inline and carried mantissas of both signs, exponents
/// near zero and, less often, far from it.
///
/// # Specification
/// - ensures: every generated value is canonical.
/// - panics: none.
/// - executable: none — a strategy is opaque to the attribute backend.
///
/// # Adequacy
/// - hypothesis: L2 — the generator feeds every differential property.
/// - witness: `tests::oracle::canonical_form_denotes_its_parts`
fn dyadic() -> impl Strategy<Value = Dyadic>
{
    let bytes = prop_oneof![
        proptest::collection::vec(any::<u8>(), 0 ..= 8),
        proptest::collection::vec(any::<u8>(), 9 ..= 24),
    ];
    let exponent = prop_oneof![-80_i32 ..= 80_i32, -0x4000_i32 ..= 0x4000_i32];
    return (bytes, any::<bool>(), exponent).prop_map(|(bytes, negative, exponent)| {
        let magnitude = BigInt::from_bytes_le(num_bigint::Sign::Plus, &bytes);
        let mantissa = if negative { magnitude.neg() } else { magnitude };
        Dyadic::new(mantissa, Exponent::from(exponent)).unwrap()
    });
}

/// Generated precisions, biased toward narrow grids where rounding loses
/// bits.
///
/// # Specification
/// - ensures: every generated precision is admitted.
/// - panics: none.
/// - executable: none — a strategy is opaque to the attribute backend.
///
/// # Adequacy
/// - hypothesis: L2 — the generator feeds every rounding property.
/// - witness: `tests::oracle::round_is_the_directed_neighbour_on_the_grid`
fn precision() -> impl Strategy<Value = Precision>
{
    return prop_oneof![1_u32 ..= 8_u32, 9_u32 ..= 64_u32, 65_u32 ..= 256_u32]
        .prop_map(|bits| Precision::try_from(bits).unwrap());
}

/// Both rounding directions.
///
/// # Specification
/// - ensures: generates each direction.
/// - panics: none.
/// - executable: none — a strategy is opaque to the attribute backend.
///
/// # Adequacy
/// - hypothesis: L2 — the generator feeds every rounding property.
/// - witness: `tests::oracle::round_is_the_directed_neighbour_on_the_grid`
fn rounding() -> impl Strategy<Value = Rounding>
{
    return prop_oneof![Just(Rounding::Floor), Just(Rounding::Ceiling)];
}

/// Pairs of positive dyadics that share their top bit, so a comparison must
/// align them.
///
/// # Specification
/// - ensures: both values lie in `[2^(t - 1), 2^t)` for one `t`.
/// - panics: none.
/// - executable: none — a strategy is opaque to the attribute backend.
///
/// # Adequacy
/// - hypothesis: L2 — the generator reaches the aligned comparison.
/// - witness: `tests::oracle::order_is_the_rational_order`
fn shared_top() -> impl Strategy<Value = (Dyadic, Dyadic)>
{
    let widths = (1_u64 ..= 150_u64, 1_u64 ..= 150_u64);
    return (widths, -40_i32 ..= 40_i32, any::<u64>(), any::<u64>()).prop_map(
        |((left_width, right_width), top, left_bits, right_bits)| {
            let value = |width: u64, bits: u64| {
                let top_bit = BigInt::from(1_u8).shl(width.checked_sub(1).unwrap());
                let low = BigInt::from(bits).rem(&top_bit);
                let mantissa = top_bit.add(low);
                let exponent = i32::try_from(
                    i64::from(top)
                        .checked_sub(i64::try_from(width).unwrap())
                        .unwrap(),
                )
                .unwrap();
                Dyadic::new(mantissa, Exponent::from(exponent)).unwrap()
            };
            (value(left_width, left_bits), value(right_width, right_bits))
        },
    );
}

/// Generated proper intervals: dyadic endpoints with either closure, and
/// rays and the whole line.
///
/// # Specification
/// - ensures: every generated interval is admitted by [`NumericInterval::new`].
/// - panics: none.
/// - executable: none — a strategy is opaque to the attribute backend.
///
/// # Adequacy
/// - hypothesis: L2 — the generator feeds every interval property; zero
///   endpoints come from the generator's zero mantissas.
/// - witness: `tests::oracle::interval_product_encloses_every_product`
fn interval() -> impl Strategy<Value = NumericInterval>
{
    let small = (
        proptest::collection::vec(any::<u8>(), 0 ..= 3),
        any::<bool>(),
        -8_i32 ..= 8_i32,
    )
        .prop_map(|(bytes, negative, exponent)| {
            let magnitude = BigInt::from_bytes_le(num_bigint::Sign::Plus, &bytes);
            let mantissa = if negative { magnitude.neg() } else { magnitude };
            Dyadic::new(mantissa, Exponent::from(exponent)).unwrap()
        });
    let closure = prop_oneof![Just(Closure::Closed), Just(Closure::Open)];
    let infinite = prop_oneof![3 => Just(false), 1 => Just(true)];
    return (
        small.clone(),
        small,
        closure.clone(),
        closure,
        infinite.clone(),
        infinite,
    )
        .prop_map(
            |(first, second, lower_closure, upper_closure, lower_infinite, upper_infinite)| {
                let (low, high) = if first <= second {
                    (first, second)
                }
                else {
                    (second, first)
                };
                let (lower_closure, upper_closure) = if low == high {
                    (Closure::Closed, Closure::Closed)
                }
                else {
                    (lower_closure, upper_closure)
                };
                let lower = if lower_infinite {
                    Bound::open(Endpoint::NegInf)
                }
                else {
                    Bound::new(Endpoint::Finite(low), lower_closure)
                };
                let upper = if upper_infinite {
                    Bound::open(Endpoint::PosInf)
                }
                else {
                    Bound::new(Endpoint::Finite(high), upper_closure)
                };
                let (lower, upper) =
                    if lower.endpoint == upper.endpoint && lower.closure != upper.closure {
                        (
                            Bound::new(lower.endpoint, Closure::Closed),
                            Bound::new(upper.endpoint, Closure::Closed),
                        )
                    }
                    else {
                        (lower, upper)
                    };
                NumericInterval::new(lower, upper, Orientation::Proper).unwrap()
            },
        );
}

/// Points of an interval to sample: each closed finite endpoint and the
/// midpoint of finite endpoints, or a point beside a single finite endpoint.
///
/// # Specification
/// - ensures: every returned point lies in the interval.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the sampled points of the enclosure properties.
/// - witness: `tests::oracle::interval_product_encloses_every_product`
#[spec(ensures: |ref result| result.iter().all(|point| interval.contains(point) == Containment::Contains))]
fn samples(interval: &NumericInterval) -> Vec<Dyadic>
{
    let exact = Precision::MAX;
    let mut points = Vec::new();
    for bound in [interval.lower(), interval.upper()] {
        if let Endpoint::Finite(ref value) = bound.endpoint
            && bound.closure == Closure::Closed
        {
            points.push(value.clone());
        }
    }
    let half = Dyadic::new(BigInt::from(1_u8), Exponent::from(-1_i32)).unwrap();
    let inner = match (&interval.lower().endpoint, &interval.upper().endpoint) {
        (&Endpoint::Finite(ref low), &Endpoint::Finite(ref high)) => low
            .add(high, exact, Rounding::Floor)
            .unwrap()
            .value()
            .mul(&half, exact, Rounding::Floor)
            .unwrap()
            .into_value(),
        (&Endpoint::Finite(ref low), _) => low
            .add(&Dyadic::ONE, exact, Rounding::Floor)
            .unwrap()
            .into_value(),
        (_, &Endpoint::Finite(ref high)) => high
            .sub(&Dyadic::ONE, exact, Rounding::Floor)
            .unwrap()
            .into_value(),
        (..) => Dyadic::ZERO,
    };
    if interval.contains(&inner) == Containment::Contains {
        points.push(inner);
    }
    return points;
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    /// The canonical form denotes the parts it was built from, and it is
    /// odd or the one zero.
    #[test]
    fn canonical_form_denotes_its_parts(bytes in proptest::collection::vec(any::<u8>(), 0..=24), negative in any::<bool>(), exponent in -200_i32..=200_i32) {
        let magnitude = BigInt::from_bytes_le(num_bigint::Sign::Plus, &bytes);
        let mantissa = if negative { magnitude.neg() } else { magnitude };
        let value = Dyadic::new(mantissa.clone(), Exponent::from(exponent)).unwrap();
        prop_assert_eq!(Rational::of(&value), Rational::scaled(mantissa, Exponent::from(exponent)));
        let parts = value.mantissa();
        if parts == BigInt::ZERO {
            prop_assert_eq!(&value, &Dyadic::ZERO);
            prop_assert_eq!(i32::from(value.exponent()), 0_i32);
        }
        else {
            prop_assert_eq!(parts.trailing_zeros(), Some(0_u64));
        }
    }

    /// Rounding is the oracle's floor or ceiling on the grid, and its
    /// exactness says whether the value moved.
    #[test]
    fn round_is_the_directed_neighbour_on_the_grid(value in dyadic(), precision in precision(), rounding in rounding()) {
        let exact = Rational::of(&value);
        let rounded = value.round(precision, rounding).unwrap();
        let expected = exact.rounded(precision, rounding);
        prop_assert_eq!(rounded.exactness() == Exactness::Exact, expected == exact);
        prop_assert_eq!(Rational::of(rounded.value()), expected);
    }

    /// A sum and a difference are the oracle's directed neighbours.
    #[test]
    fn sum_and_difference_are_the_directed_neighbours(left in dyadic(), right in dyadic(), precision in precision(), rounding in rounding()) {
        let sum = left.add(&right, precision, rounding).unwrap();
        let exact = Rational::of(&left).plus(&Rational::of(&right));
        prop_assert_eq!(Rational::of(sum.value()), exact.rounded(precision, rounding));
        prop_assert_eq!(sum.exactness() == Exactness::Exact, Rational::of(sum.value()) == exact);
        let difference = left.sub(&right, precision, rounding).unwrap();
        let exact = Rational::of(&left).minus(&Rational::of(&right));
        prop_assert_eq!(Rational::of(difference.value()), exact.rounded(precision, rounding));
        prop_assert_eq!(difference.exactness() == Exactness::Exact, Rational::of(difference.value()) == exact);
    }

    /// An operand far below the other rounds the sum by its sign alone, on
    /// both sides of the sticky threshold.
    #[test]
    fn far_operands_round_by_their_sign(big in dyadic(), small_bytes in proptest::collection::vec(any::<u8>(), 1..=8), negative in any::<bool>(), gap in 0_i32..=400_i32, precision in precision(), rounding in rounding()) {
        let magnitude = BigInt::from_bytes_le(num_bigint::Sign::Plus, &small_bytes);
        let mantissa = if negative { magnitude.neg() } else { magnitude };
        let exponent = i32::from(big.exponent()).checked_sub(gap).unwrap();
        let small = Dyadic::new(mantissa, Exponent::from(exponent)).unwrap();
        for (left, right) in [(&big, &small), (&small, &big)] {
            let sum = left.add(right, precision, rounding).unwrap();
            let exact = Rational::of(left).plus(&Rational::of(right));
            prop_assert_eq!(Rational::of(sum.value()), exact.rounded(precision, rounding));
            let difference = left.sub(right, precision, rounding).unwrap();
            let exact = Rational::of(left).minus(&Rational::of(right));
            prop_assert_eq!(Rational::of(difference.value()), exact.rounded(precision, rounding));
        }
    }

    /// A product is the oracle's directed neighbour.
    #[test]
    fn product_is_the_directed_neighbour(left in dyadic(), right in dyadic(), precision in precision(), rounding in rounding()) {
        let product = left.mul(&right, precision, rounding).unwrap();
        let exact = Rational::of(&left).times(&Rational::of(&right));
        prop_assert_eq!(Rational::of(product.value()), exact.rounded(precision, rounding));
        prop_assert_eq!(product.exactness() == Exactness::Exact, Rational::of(product.value()) == exact);
    }

    /// The order is the rational order, on arbitrary pairs and on pairs
    /// that share their top bit, of both signs.
    #[test]
    fn order_is_the_rational_order(left in dyadic(), right in dyadic(), shared in shared_top()) {
        prop_assert_eq!(left.cmp(&right), Rational::of(&left).order(&Rational::of(&right)));
        let (first, second) = shared;
        prop_assert_eq!(first.cmp(&second), Rational::of(&first).order(&Rational::of(&second)));
        let (first, second) = ((&first).neg(), (&second).neg());
        prop_assert_eq!(first.cmp(&second), Rational::of(&first).order(&Rational::of(&second)));
    }

    /// An interval sum and difference round their exact endpoints outward,
    /// close an endpoint exactly when both operands close theirs and the
    /// rounding is exact, and contain every sampled sum.
    #[test]
    fn interval_sum_and_difference_round_outward(left in interval(), right in interval(), precision in precision()) {
        let attained = |first: &Bound, second: &Bound| if first.closure == Closure::Closed && second.closure == Closure::Closed { Closure::Closed } else { Closure::Open };
        let sum = left.add(&right, precision).unwrap();
        let lower = match (Extended::of(&left.lower().endpoint), Extended::of(&right.lower().endpoint)) {
            (Extended::Finite(x), Extended::Finite(y)) => Extended::Finite(x.plus(&y)),
            _ => Extended::NegInf,
        };
        let upper = match (Extended::of(&left.upper().endpoint), Extended::of(&right.upper().endpoint)) {
            (Extended::Finite(x), Extended::Finite(y)) => Extended::Finite(x.plus(&y)),
            _ => Extended::PosInf,
        };
        prop_assert_eq!(observed(sum.lower()), expected(&lower, attained(left.lower(), right.lower()), precision, Rounding::Floor));
        prop_assert_eq!(observed(sum.upper()), expected(&upper, attained(left.upper(), right.upper()), precision, Rounding::Ceiling));
        let difference = left.sub(&right, precision).unwrap();
        let lower = match (Extended::of(&left.lower().endpoint), Extended::of(&right.upper().endpoint)) {
            (Extended::Finite(x), Extended::Finite(y)) => Extended::Finite(x.minus(&y)),
            _ => Extended::NegInf,
        };
        let upper = match (Extended::of(&left.upper().endpoint), Extended::of(&right.lower().endpoint)) {
            (Extended::Finite(x), Extended::Finite(y)) => Extended::Finite(x.minus(&y)),
            _ => Extended::PosInf,
        };
        prop_assert_eq!(observed(difference.lower()), expected(&lower, attained(left.lower(), right.upper()), precision, Rounding::Floor));
        prop_assert_eq!(observed(difference.upper()), expected(&upper, attained(left.upper(), right.lower()), precision, Rounding::Ceiling));
        for x in samples(&left) {
            for y in samples(&right) {
                let exact_sum = x.add(&y, Precision::MAX, Rounding::Floor).unwrap().into_value();
                prop_assert_eq!(sum.contains(&exact_sum), Containment::Contains);
                let exact_difference = x.sub(&y, Precision::MAX, Rounding::Floor).unwrap().into_value();
                prop_assert_eq!(difference.contains(&exact_difference), Containment::Contains);
            }
        }
    }

    /// An interval product's endpoints are the extremes of all four exact
    /// endpoint products, rounded outward, closed exactly when attained and
    /// exact, and the product contains every sampled product.
    #[test]
    fn interval_product_encloses_every_product(left in interval(), right in interval(), precision in precision()) {
        let product = left.mul(&right, precision).unwrap();
        let zero = |interval: &NumericInterval| interval.contains(&Dyadic::ZERO) == Containment::Contains;
        let zero_inside = zero(&left) || zero(&right);
        let mut corners = Vec::new();
        for x in [left.lower(), left.upper()] {
            for y in [right.lower(), right.upper()] {
                let value = Extended::of(&x.endpoint).times(&Extended::of(&y.endpoint));
                let is_zero = value == Extended::Finite(Rational::reduced(BigInt::ZERO, BigInt::from(1_u8)));
                let closed = matches!(value, Extended::Finite(_))
                    && ((x.closure == Closure::Closed && y.closure == Closure::Closed) || (is_zero && zero_inside));
                corners.push((value, if closed { Closure::Closed } else { Closure::Open }));
            }
        }
        let extreme = |towards: Ordering| {
            let mut best = corners[0].clone();
            for candidate in &corners[1..] {
                match candidate.0.order(&best.0) {
                    order if order == towards => best = candidate.clone(),
                    Ordering::Equal if candidate.1 == Closure::Closed => best.1 = Closure::Closed,
                    Ordering::Less | Ordering::Equal | Ordering::Greater => {}
                }
            }
            best
        };
        let (lower, lower_attained) = extreme(Ordering::Less);
        let (upper, upper_attained) = extreme(Ordering::Greater);
        prop_assert_eq!(observed(product.lower()), expected(&lower, lower_attained, precision, Rounding::Floor));
        prop_assert_eq!(observed(product.upper()), expected(&upper, upper_attained, precision, Rounding::Ceiling));
        for x in samples(&left) {
            for y in samples(&right) {
                let exact = x.mul(&y, Precision::MAX, Rounding::Floor).unwrap().into_value();
                prop_assert_eq!(product.contains(&exact), Containment::Contains);
            }
        }
    }
}
