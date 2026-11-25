//! Boundary witnesses of the interval domain: each refusal by name, points
//! and rays, the dual involution, containment at each closure, the refused
//! dual operand, where a product attains zero, the refused divisor that holds
//! zero, and the rendering of each failure.

use gandr_theory_exact_reals::Bound;
use gandr_theory_exact_reals::Closure;
use gandr_theory_exact_reals::Containment;
use gandr_theory_exact_reals::Dyadic;
use gandr_theory_exact_reals::DyadicError;
use gandr_theory_exact_reals::Endpoint;
use gandr_theory_exact_reals::IntervalError;
use gandr_theory_exact_reals::NumericInterval;
use gandr_theory_exact_reals::Orientation;
use gandr_theory_exact_reals::Precision;

/// The finite endpoint of an integer.
///
/// # Specification
/// trivial.
fn at(value: Dyadic) -> Endpoint
{
    return Endpoint::Finite(value);
}

/// The proper interval between two bounds, which must be admitted.
///
/// # Specification
/// trivial.
fn proper(
    lower: Bound,
    upper: Bound,
) -> NumericInterval
{
    return NumericInterval::new(lower, upper, Orientation::Proper).unwrap();
}

#[test]
fn errors_render_one_distinct_line()
{
    let arithmetic = IntervalError::Arithmetic(DyadicError::ExponentOutOfRange);
    let errors = [
        IntervalError::ClosedInfinity,
        IntervalError::Reversed,
        IntervalError::Empty,
        IntervalError::DualOperand,
        IntervalError::ZeroDivisor,
        arithmetic,
    ];
    let lines = errors.map(|error| error.to_string());
    for (index, line) in lines.iter().enumerate() {
        assert!(
            !line.is_empty() && !line.contains('\n'),
            "not one line: {line}"
        );
        assert!(
            lines
                .iter()
                .skip(index.checked_add(1).unwrap())
                .all(|other| other != line),
            "a repeated line: {line}"
        );
    }
    assert!(lines[5].contains(&DyadicError::ExponentOutOfRange.to_string()));
}

#[test]
fn quotient_refuses_a_divisor_holding_zero()
{
    let precision = Precision::try_from(16_u32).unwrap();
    let one = Dyadic::from(1_i64);
    let dividend = NumericInterval::point(one.clone());
    let holding = [
        NumericInterval::point(Dyadic::ZERO),
        proper(Bound::closed(Dyadic::ZERO), Bound::closed(one.clone())),
        proper(
            Bound::open(at(Dyadic::from(-1_i64))),
            Bound::closed(Dyadic::ZERO),
        ),
        proper(
            Bound::open(at(Dyadic::from(-1_i64))),
            Bound::open(at(one.clone())),
        ),
        NumericInterval::whole(),
    ];
    for divisor in &holding {
        assert_eq!(
            dividend.div(divisor, precision),
            Err(IntervalError::ZeroDivisor)
        );
    }
    let beside = proper(Bound::open(at(Dyadic::ZERO)), Bound::closed(one.clone()));
    let quotient = dividend.div(&beside, precision).unwrap();
    assert_eq!(quotient.lower(), &Bound::closed(one));
    assert_eq!(quotient.upper(), &Bound::open(Endpoint::PosInf));
}

#[test]
fn new_refuses_each_malformed_interval_by_name()
{
    let one = Dyadic::from(1_i64);
    let two = Dyadic::from(2_i64);
    let closed_infinity = NumericInterval::new(
        Bound::new(Endpoint::NegInf, Closure::Closed),
        Bound::closed(one.clone()),
        Orientation::Proper,
    );
    assert_eq!(closed_infinity, Err(IntervalError::ClosedInfinity));
    let closed_infinity = NumericInterval::new(
        Bound::closed(one.clone()),
        Bound::new(Endpoint::PosInf, Closure::Closed),
        Orientation::Proper,
    );
    assert_eq!(closed_infinity, Err(IntervalError::ClosedInfinity));
    // The closure check runs before the order check.
    let both = NumericInterval::new(
        Bound::new(Endpoint::PosInf, Closure::Closed),
        Bound::closed(one.clone()),
        Orientation::Proper,
    );
    assert_eq!(both, Err(IntervalError::ClosedInfinity));
    let reversed = NumericInterval::new(
        Bound::closed(two.clone()),
        Bound::closed(one.clone()),
        Orientation::Proper,
    );
    assert_eq!(reversed, Err(IntervalError::Reversed));
    let reversed = NumericInterval::new(
        Bound::closed(one.clone()),
        Bound::closed(two),
        Orientation::Dual,
    );
    assert_eq!(reversed, Err(IntervalError::Reversed));
    let empty = NumericInterval::new(
        Bound::closed(one.clone()),
        Bound::open(at(one.clone())),
        Orientation::Proper,
    );
    assert_eq!(empty, Err(IntervalError::Empty));
    let empty = NumericInterval::new(
        Bound::open(at(one.clone())),
        Bound::closed(one.clone()),
        Orientation::Dual,
    );
    assert_eq!(empty, Err(IntervalError::Empty));
    let empty = NumericInterval::new(
        Bound::open(Endpoint::PosInf),
        Bound::open(Endpoint::PosInf),
        Orientation::Proper,
    );
    assert_eq!(empty, Err(IntervalError::Empty));
    let reversed = NumericInterval::new(
        Bound::open(Endpoint::PosInf),
        Bound::closed(one),
        Orientation::Proper,
    );
    assert_eq!(reversed, Err(IntervalError::Reversed));
}

#[test]
fn new_admits_points_and_rays()
{
    let one = Dyadic::from(1_i64);
    let point = proper(Bound::closed(one.clone()), Bound::closed(one.clone()));
    assert_eq!(point, NumericInterval::point(one.clone()));
    let dual_point = NumericInterval::new(
        Bound::closed(one.clone()),
        Bound::closed(one.clone()),
        Orientation::Dual,
    )
    .unwrap();
    assert_eq!(dual_point.orientation(), Orientation::Dual);
    let ray = proper(Bound::open(Endpoint::NegInf), Bound::closed(one));
    assert_eq!(ray.lower().endpoint, Endpoint::NegInf);
    let line = proper(Bound::open(Endpoint::NegInf), Bound::open(Endpoint::PosInf));
    assert_eq!(line.contains(&Dyadic::ZERO), Containment::Contains);
    let whole_dual = NumericInterval::new(
        Bound::open(Endpoint::PosInf),
        Bound::open(Endpoint::NegInf),
        Orientation::Dual,
    );
    assert!(whole_dual.is_ok());
}

#[test]
fn dual_is_a_valid_involution()
{
    let one = Dyadic::from(1_i64);
    let two = Dyadic::from(2_i64);
    let cases = [
        proper(Bound::closed(one.clone()), Bound::open(at(two.clone()))),
        proper(Bound::open(Endpoint::NegInf), Bound::closed(two)),
        NumericInterval::point(one),
        proper(Bound::open(Endpoint::NegInf), Bound::open(Endpoint::PosInf)),
    ];
    for interval in cases {
        let dual = interval.clone().dual();
        assert_eq!(dual.orientation(), Orientation::Dual);
        assert_eq!(dual.lower(), interval.upper());
        let rebuilt = NumericInterval::new(
            dual.lower().clone(),
            dual.upper().clone(),
            dual.orientation(),
        );
        assert_eq!(rebuilt.as_ref(), Ok(&dual));
        assert_eq!(dual.contains(&Dyadic::ZERO), Containment::Improper);
        assert_eq!(dual.dual(), interval);
    }
}

#[test]
fn containment_reads_each_closure()
{
    let one = Dyadic::from(1_i64);
    let two = Dyadic::from(2_i64);
    let three = Dyadic::from(3_i64);
    let half_open = proper(Bound::closed(one.clone()), Bound::open(at(two.clone())));
    assert_eq!(half_open.contains(&one), Containment::Contains);
    assert_eq!(half_open.contains(&two), Containment::Excludes);
    assert_eq!(half_open.contains(&Dyadic::ZERO), Containment::Excludes);
    let open_closed = proper(Bound::open(at(one.clone())), Bound::closed(two.clone()));
    assert_eq!(open_closed.contains(&one), Containment::Excludes);
    assert_eq!(open_closed.contains(&two), Containment::Contains);
    assert_eq!(open_closed.contains(&three), Containment::Excludes);
    let ray = proper(Bound::open(at(one)), Bound::open(Endpoint::PosInf));
    assert_eq!(ray.contains(&three), Containment::Contains);
    assert_eq!(ray.contains(&Dyadic::ZERO), Containment::Excludes);
}

#[test]
fn arithmetic_refuses_a_dual_operand()
{
    let one = Dyadic::from(1_i64);
    let two = Dyadic::from(2_i64);
    let proper_interval = proper(Bound::closed(one.clone()), Bound::closed(two.clone()));
    let dual =
        NumericInterval::new(Bound::closed(two), Bound::closed(one), Orientation::Dual).unwrap();
    let precision = Precision::MAX;
    for (left, right) in [(&proper_interval, &dual), (&dual, &proper_interval)] {
        assert_eq!(left.add(right, precision), Err(IntervalError::DualOperand));
        assert_eq!(left.sub(right, precision), Err(IntervalError::DualOperand));
        assert_eq!(left.mul(right, precision), Err(IntervalError::DualOperand));
    }
}

#[test]
fn product_attains_zero_only_through_an_operand()
{
    let one = Dyadic::from(1_i64);
    let precision = Precision::MAX;
    let ray = proper(Bound::closed(one.clone()), Bound::open(Endpoint::PosInf));
    // `(0, 1] · [1, ∞) = (0, ∞)`: neither operand holds zero.
    let open_unit = proper(Bound::open(at(Dyadic::ZERO)), Bound::closed(one.clone()));
    let product = open_unit.mul(&ray, precision).unwrap();
    assert_eq!(product.lower(), &Bound::open(at(Dyadic::ZERO)));
    assert_eq!(product.upper(), &Bound::open(Endpoint::PosInf));
    // `[0, 1] · [1, ∞) = [0, ∞)`: zero times a finite element.
    let closed_unit = proper(Bound::closed(Dyadic::ZERO), Bound::closed(one));
    let product = closed_unit.mul(&ray, precision).unwrap();
    assert_eq!(product.lower(), &Bound::closed(Dyadic::ZERO));
    // `[0, 0] · (-∞, ∞) = [0, 0]`: zero times an infinity is zero.
    let line = proper(Bound::open(Endpoint::NegInf), Bound::open(Endpoint::PosInf));
    let product = NumericInterval::point(Dyadic::ZERO)
        .mul(&line, precision)
        .unwrap();
    assert_eq!(product, NumericInterval::point(Dyadic::ZERO));
    // `[-1, 0) · [1, ∞) = (-∞, 0)`: a negative element times an infinity.
    let below = proper(
        Bound::closed(Dyadic::from(-1_i64)),
        Bound::open(at(Dyadic::ZERO)),
    );
    let product = below.mul(&ray, precision).unwrap();
    assert_eq!(product.lower(), &Bound::open(Endpoint::NegInf));
    assert_eq!(product.upper(), &Bound::open(at(Dyadic::ZERO)));
}
