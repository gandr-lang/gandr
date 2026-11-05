//! Explicitly oriented intervals with outward-rounded arithmetic.
//!
//! A refinement step needs a set that certainly contains an unknown real.
//! An interval with dyadic endpoints is such a set, and it stays sound under
//! arithmetic when each endpoint rounds away from the set. [`NumericInterval`]
//! holds two [`Bound`]s, each an [`Endpoint`] with a [`Closure`], and an
//! [`Orientation`].
//!
//! A proper interval has its lower endpoint at or below its upper endpoint. A
//! dual interval, the improper interval of Kaucher arithmetic, has them in
//! the other order. The orientation is a tag: an interval is never reordered
//! to become proper. The invariants of a dual interval are those of a proper
//! interval with the order reversed, so [`NumericInterval::dual`] is an
//! involution that never fails.
//!
//! An infinite endpoint is always open. Two equal endpoints are a point and
//! must both be closed. [`NumericInterval::new`] refuses every other form by
//! name. The arithmetic takes proper operands. A result endpoint that lost
//! bits to rounding is open, and so is an endpoint that the operands do not
//! attain. The product attains zero exactly when an operand contains zero.
//! At an infinite endpoint, the product of zero and an infinity is zero,
//! because every element of an interval is finite.

use core::cmp::Ordering;
use core::fmt;

use anodized::spec;

use crate::dyadic::Dyadic;
use crate::dyadic::DyadicError;
use crate::dyadic::Exactness;
use crate::dyadic::Precision;
use crate::dyadic::Rounding;
use crate::dyadic::Sign;
use crate::dyadic::Unrounded;

/// An endpoint of an interval: a dyadic, or one of the two infinities.
///
/// The derived order is the order of the extended real line.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Endpoint
{
    /// Below every dyadic.
    NegInf,
    /// A dyadic.
    Finite(Dyadic),
    /// Above every dyadic.
    PosInf,
}

/// Whether an interval contains its endpoint.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Closure
{
    /// The endpoint belongs to the interval.
    Closed,
    /// The endpoint does not belong to the interval.
    Open,
}

/// The orientation of an interval.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Orientation
{
    /// The lower endpoint lies at or below the upper endpoint.
    Proper,
    /// The lower endpoint lies at or above the upper endpoint: the improper
    /// interval of Kaucher arithmetic.
    Dual,
}

/// Whether an interval contains a dyadic.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Containment
{
    /// The proper interval contains the dyadic.
    Contains,
    /// The proper interval does not contain the dyadic.
    Excludes,
    /// The interval is dual and denotes no set of reals.
    Improper,
}

/// One end of an interval: its endpoint and whether the interval contains
/// it.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Bound
{
    /// The endpoint.
    pub endpoint: Endpoint,
    /// Whether the interval contains the endpoint.
    pub closure: Closure,
}

impl Bound
{
    /// The bound at `endpoint` with `closure`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn new(
        endpoint: Endpoint,
        closure: Closure,
    ) -> Self
    {
        return Self { endpoint, closure };
    }

    /// The closed bound at the dyadic `value`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn closed(value: Dyadic) -> Self
    {
        return Self {
            endpoint: Endpoint::Finite(value),
            closure: Closure::Closed,
        };
    }

    /// The open bound at `endpoint`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn open(endpoint: Endpoint) -> Self
    {
        return Self {
            endpoint,
            closure: Closure::Open,
        };
    }
}

/// A malformed interval, or a failed interval operation.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum IntervalError
{
    /// An infinite endpoint is marked closed.
    ClosedInfinity,
    /// The endpoints lie in the order opposite to the orientation.
    Reversed,
    /// The endpoints are equal and not both closed, so the interval holds no
    /// point.
    Empty,
    /// An operand of the arithmetic is dual.
    DualOperand,
    /// An endpoint operation failed.
    Arithmetic(DyadicError),
}

impl From<DyadicError> for IntervalError
{
    /// Wrap a failed endpoint operation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(error: DyadicError) -> Self
    {
        return Self::Arithmetic(error);
    }
}

impl fmt::Display for IntervalError
{
    /// Write the failure as one line.
    ///
    /// # Specification
    /// - ensures: writes one fixed line per variant that names the failure, and
    ///   an endpoint failure's line names the dyadic failure.
    /// - fails: passes the formatter's own write failure on unchanged.
    /// - panics: none.
    /// - executable: none — a `Display` sink: the formatter is write-only.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each variant renders one distinct line, and the
    ///   wording is not pinned.
    /// - witness: `tests::interval::errors_render_one_distinct_line`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::ClosedInfinity => f.write_str("an infinite endpoint is closed"),
            Self::Reversed => {
                f.write_str("the endpoints are in the order opposite to the orientation")
            },
            Self::Empty => f.write_str("the endpoints are equal and not both closed"),
            Self::DualOperand => f.write_str("an operand of interval arithmetic is dual"),
            Self::Arithmetic(error) => write!(f, "an endpoint operation failed: {error}"),
        }
    }
}

impl core::error::Error for IntervalError
{
}

/// An interval with dyadic or infinite endpoints, each endpoint's closure,
/// and an explicit orientation.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct NumericInterval
{
    /// The lower bound.
    lower: Bound,
    /// The upper bound.
    upper: Bound,
    /// Whether the bounds lie in proper or in dual order.
    orientation: Orientation,
}

impl NumericInterval
{
    /// The interval from `lower` to `upper` with `orientation`, validated.
    ///
    /// # Specification
    /// - ensures: returns the interval when each infinite endpoint is open, the
    ///   endpoints lie in the orientation's order, and equal endpoints are both
    ///   closed.
    /// - fails: refuses each malformed interval by name, the checks in this
    ///   order: [`IntervalError::ClosedInfinity`], then
    ///   [`IntervalError::Reversed`], then [`IntervalError::Empty`].
    /// - panics: none.
    ///
    /// # Errors
    /// - [`IntervalError::ClosedInfinity`]: an infinite endpoint is closed.
    /// - [`IntervalError::Reversed`]: a proper interval's lower endpoint lies
    ///   above its upper endpoint, or a dual interval's lies below.
    /// - [`IntervalError::Empty`]: the endpoints are equal and not both closed.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each refusal on its smallest trigger and at the
    ///   boundary beside it, in both orientations: an equal pair closed and
    ///   half-open, a reversed pair by one unit, an infinity closed on either
    ///   side.
    /// - witness: `tests::interval::new_refuses_each_malformed_interval_by_name`
    /// - witness: `tests::interval::new_admits_points_and_rays`
    #[inline]
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |interval| interval.orientation == orientation))]
    pub fn new(
        lower: Bound,
        upper: Bound,
        orientation: Orientation,
    ) -> Result<Self, IntervalError>
    {
        for bound in [&lower, &upper] {
            if bound.closure == Closure::Closed && !matches!(bound.endpoint, Endpoint::Finite(_)) {
                return Err(IntervalError::ClosedInfinity);
            }
        }
        let (low, high) = match orientation {
            Orientation::Proper => (&lower, &upper),
            Orientation::Dual => (&upper, &lower),
        };
        match low.endpoint.cmp(&high.endpoint) {
            Ordering::Less => {},
            Ordering::Equal
                if low.closure == Closure::Closed && high.closure == Closure::Closed => {},
            Ordering::Equal => return Err(IntervalError::Empty),
            Ordering::Greater => return Err(IntervalError::Reversed),
        }
        return Ok(Self {
            lower,
            upper,
            orientation,
        });
    }

    /// The proper closed interval holding the one dyadic `value`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn point(value: Dyadic) -> Self
    {
        return Self {
            lower: Bound::closed(value.clone()),
            upper: Bound::closed(value),
            orientation: Orientation::Proper,
        };
    }

    /// The lower bound.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn lower(&self) -> &Bound
    {
        return &self.lower;
    }

    /// The upper bound.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn upper(&self) -> &Bound
    {
        return &self.upper;
    }

    /// The orientation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn orientation(&self) -> Orientation
    {
        return self.orientation;
    }

    /// The dual interval: the bounds exchanged and the orientation flipped.
    ///
    /// # Specification
    /// - ensures: the result's lower bound is this interval's upper bound, its
    ///   upper bound this lower bound, and its orientation the other one.
    ///   Applied twice it gives the interval back.
    /// - panics: none.
    /// - intension: moves the bounds; nothing is copied or allocated.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a proper, a dual, a ray and a point; the result
    ///   passes the validating constructor, and the double dual is the
    ///   identity.
    /// - witness: `tests::interval::dual_is_a_valid_involution`
    #[inline]
    #[must_use]
    #[spec(captures: [orientation = self.orientation, lower = self.lower.closure, upper = self.upper.closure], ensures: |ref result| result.orientation != orientation && result.lower.closure == upper && result.upper.closure == lower)]
    pub fn dual(self) -> Self
    {
        let orientation = match self.orientation {
            Orientation::Proper => Orientation::Dual,
            Orientation::Dual => Orientation::Proper,
        };
        return Self {
            lower: self.upper,
            upper: self.lower,
            orientation,
        };
    }

    /// Whether the interval contains the dyadic `value`.
    ///
    /// # Specification
    /// - ensures: returns [`Containment::Improper`] for a dual interval;
    ///   otherwise [`Containment::Contains`] exactly when `value` lies strictly
    ///   inside or on a closed endpoint.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the value on each endpoint, closed and open, one unit
    ///   inside and outside, and against both infinities.
    /// - witness: `tests::interval::containment_reads_each_closure`
    #[inline]
    #[must_use]
    #[spec(ensures: |ref result| (*result == Containment::Improper) == (self.orientation == Orientation::Dual))]
    pub fn contains(
        &self,
        value: &Dyadic,
    ) -> Containment
    {
        if self.orientation == Orientation::Dual {
            return Containment::Improper;
        }
        let above_lower = match against(&self.lower.endpoint, value) {
            Ordering::Less => true,
            Ordering::Equal => self.lower.closure == Closure::Closed,
            Ordering::Greater => false,
        };
        let below_upper = match against(&self.upper.endpoint, value) {
            Ordering::Greater => true,
            Ordering::Equal => self.upper.closure == Closure::Closed,
            Ordering::Less => false,
        };
        return if above_lower && below_upper {
            Containment::Contains
        }
        else {
            Containment::Excludes
        };
    }

    /// The interval sum, rounded outward to `precision` bits.
    ///
    /// # Specification
    /// - ensures: returns a proper interval containing `x + y` for every `x` in
    ///   `self` and `y` in `other`. Each finite endpoint is the directed
    ///   rounding of the exact endpoint sum, and it is closed exactly when both
    ///   operand endpoints are closed and the rounding was exact.
    /// - fails: returns [`IntervalError::DualOperand`] when an operand is dual,
    ///   and [`IntervalError::Arithmetic`] when an endpoint's exponent leaves
    ///   its range.
    /// - panics: none.
    /// - intension: two endpoint sums, so the cost is twice that of one
    ///   [`Dyadic::add`].
    ///
    /// # Errors
    /// - [`IntervalError::DualOperand`]: an operand is dual.
    /// - [`IntervalError::Arithmetic`]: an endpoint sum failed.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the rational oracle forms the exact endpoint sums,
    ///   rounds them, and checks each closure; sampled points of both operands
    ///   land inside the result. L3 — a dual operand.
    /// - witness: `tests::oracle::interval_sum_and_difference_round_outward`
    /// - witness: `tests::interval::arithmetic_refuses_a_dual_operand`
    #[inline]
    #[spec(ensures: |ref result| result.as_ref().map_or_else(
        |error| *error != IntervalError::DualOperand || self.orientation == Orientation::Dual || other.orientation == Orientation::Dual,
        |sum| sum.orientation == Orientation::Proper && Self::new(sum.lower.clone(), sum.upper.clone(), sum.orientation).is_ok(),
    ))]
    pub fn add(
        &self,
        other: &Self,
        precision: Precision,
    ) -> Result<Self, IntervalError>
    {
        self.require_proper(other)?;
        let lower = extended_sum(
            &self.lower,
            &other.lower,
            Polarity::Keep,
            precision,
            Rounding::Floor,
        )?;
        let upper = extended_sum(
            &self.upper,
            &other.upper,
            Polarity::Keep,
            precision,
            Rounding::Ceiling,
        )?;
        return Ok(Self {
            lower,
            upper,
            orientation: Orientation::Proper,
        });
    }

    /// The interval difference, rounded outward to `precision` bits.
    ///
    /// # Specification
    /// - ensures: returns a proper interval containing `x - y` for every `x` in
    ///   `self` and `y` in `other`: its lower endpoint rounds `self`'s lower
    ///   minus `other`'s upper down, its upper endpoint rounds `self`'s upper
    ///   minus `other`'s lower up.
    /// - fails: returns [`IntervalError::DualOperand`] when an operand is dual,
    ///   and [`IntervalError::Arithmetic`] when an endpoint's exponent leaves
    ///   its range.
    /// - panics: none.
    /// - intension: two endpoint differences.
    ///
    /// # Errors
    /// - [`IntervalError::DualOperand`]: an operand is dual.
    /// - [`IntervalError::Arithmetic`]: an endpoint difference failed.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the rational oracle forms the exact crossed endpoint
    ///   differences; a mutant that pairs lower with lower disagrees with it.
    /// - witness: `tests::oracle::interval_sum_and_difference_round_outward`
    #[inline]
    #[spec(ensures: |ref result| result.as_ref().map_or_else(
        |error| *error != IntervalError::DualOperand || self.orientation == Orientation::Dual || other.orientation == Orientation::Dual,
        |difference| difference.orientation == Orientation::Proper && Self::new(difference.lower.clone(), difference.upper.clone(), difference.orientation).is_ok(),
    ))]
    pub fn sub(
        &self,
        other: &Self,
        precision: Precision,
    ) -> Result<Self, IntervalError>
    {
        self.require_proper(other)?;
        let lower = extended_sum(
            &self.lower,
            &other.upper,
            Polarity::Flip,
            precision,
            Rounding::Floor,
        )?;
        let upper = extended_sum(
            &self.upper,
            &other.lower,
            Polarity::Flip,
            precision,
            Rounding::Ceiling,
        )?;
        return Ok(Self {
            lower,
            upper,
            orientation: Orientation::Proper,
        });
    }

    /// The interval product, rounded outward to `precision` bits.
    ///
    /// # Specification
    /// - ensures: returns a proper interval containing `x · y` for every `x` in
    ///   `self` and `y` in `other`. Its endpoints are the exact least and
    ///   greatest endpoint products, rounded outward. An endpoint is closed
    ///   exactly when the rounding was exact and some pair of elements attains
    ///   it.
    /// - fails: returns [`IntervalError::DualOperand`] when an operand is dual,
    ///   and [`IntervalError::Arithmetic`] when an endpoint's exponent leaves
    ///   its range.
    /// - panics: none.
    /// - intension: the signs of the operands select the endpoint products. Two
    ///   products are formed, or four when both operands straddle zero.
    ///
    /// # Errors
    /// - [`IntervalError::DualOperand`]: an operand is dual.
    /// - [`IntervalError::Arithmetic`]: an endpoint product failed.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the rational oracle forms all four endpoint products
    ///   and takes their extremes, independently of the sign table; sampled
    ///   points land inside the result. Generated operands cover the nine sign
    ///   classes, zero endpoints of both closures, and infinities. A mutant
    ///   that swaps a table entry disagrees with it.
    /// - witness: `tests::oracle::interval_product_encloses_every_product`
    /// - witness: `tests::interval::product_attains_zero_only_through_an_operand`
    #[inline]
    #[spec(ensures: |ref result| result.as_ref().map_or_else(
        |error| *error != IntervalError::DualOperand || self.orientation == Orientation::Dual || other.orientation == Orientation::Dual,
        |product| product.orientation == Orientation::Proper && Self::new(product.lower.clone(), product.upper.clone(), product.orientation).is_ok(),
    ))]
    pub fn mul(
        &self,
        other: &Self,
        precision: Precision,
    ) -> Result<Self, IntervalError>
    {
        self.require_proper(other)?;
        let (lower, upper) = match (self.class(), other.class()) {
            (Class::Positive, Class::Positive) => (
                Corners::One(Side::Lower, Side::Lower),
                Corners::One(Side::Upper, Side::Upper),
            ),
            (Class::Positive, Class::Negative) => (
                Corners::One(Side::Upper, Side::Lower),
                Corners::One(Side::Lower, Side::Upper),
            ),
            (Class::Positive, Class::Mixed) => (
                Corners::One(Side::Upper, Side::Lower),
                Corners::One(Side::Upper, Side::Upper),
            ),
            (Class::Negative, Class::Positive) => (
                Corners::One(Side::Lower, Side::Upper),
                Corners::One(Side::Upper, Side::Lower),
            ),
            (Class::Negative, Class::Negative) => (
                Corners::One(Side::Upper, Side::Upper),
                Corners::One(Side::Lower, Side::Lower),
            ),
            (Class::Negative, Class::Mixed) => (
                Corners::One(Side::Lower, Side::Upper),
                Corners::One(Side::Lower, Side::Lower),
            ),
            (Class::Mixed, Class::Positive) => (
                Corners::One(Side::Lower, Side::Upper),
                Corners::One(Side::Upper, Side::Upper),
            ),
            (Class::Mixed, Class::Negative) => (
                Corners::One(Side::Upper, Side::Lower),
                Corners::One(Side::Lower, Side::Lower),
            ),
            (Class::Mixed, Class::Mixed) => (
                Corners::Two([(Side::Lower, Side::Upper), (Side::Upper, Side::Lower)]),
                Corners::Two([(Side::Lower, Side::Lower), (Side::Upper, Side::Upper)]),
            ),
        };
        let lower = self.extreme(other, lower, Ordering::Less)?;
        let upper = self.extreme(other, upper, Ordering::Greater)?;
        let lower = lower.rounded(precision, Rounding::Floor)?;
        let upper = upper.rounded(precision, Rounding::Ceiling)?;
        return Ok(Self {
            lower,
            upper,
            orientation: Orientation::Proper,
        });
    }

    /// Refuse a dual operand.
    ///
    /// # Specification
    /// - ensures: succeeds when both intervals are proper.
    /// - fails: returns [`IntervalError::DualOperand`] when either is dual.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`IntervalError::DualOperand`]: an operand is dual.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a dual operand on each side of each operation.
    /// - witness: `tests::interval::arithmetic_refuses_a_dual_operand`
    #[spec(ensures: |ref result| result.is_ok() == (self.orientation == Orientation::Proper && other.orientation == Orientation::Proper))]
    fn require_proper(
        &self,
        other: &Self,
    ) -> Result<(), IntervalError>
    {
        if self.orientation == Orientation::Dual || other.orientation == Orientation::Dual {
            return Err(IntervalError::DualOperand);
        }
        return Ok(());
    }

    /// The sign class of a proper interval.
    ///
    /// # Specification
    /// - requires: the interval is proper.
    /// - ensures: [`Class::Positive`] when the lower endpoint is at or above
    ///   zero, else [`Class::Negative`] when the upper endpoint is at or below
    ///   zero, else [`Class::Mixed`].
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the product's oracle crosses all nine class pairs,
    ///   with endpoints at zero.
    /// - witness: `tests::oracle::interval_product_encloses_every_product`
    #[spec(requires: self.orientation == Orientation::Proper)]
    fn class(&self) -> Class
    {
        if endpoint_sign(&self.lower.endpoint) != Sign::Negative {
            return Class::Positive;
        }
        if endpoint_sign(&self.upper.endpoint) != Sign::Positive {
            return Class::Negative;
        }
        return Class::Mixed;
    }

    /// The bound on `side`.
    ///
    /// # Specification
    /// trivial.
    const fn bound(
        &self,
        side: Side,
    ) -> &Bound
    {
        return match side {
            Side::Lower => &self.lower,
            Side::Upper => &self.upper,
        };
    }

    /// The least or the greatest of the endpoint products that `corners`
    /// name.
    ///
    /// # Specification
    /// - ensures: returns the candidate whose value is extreme in the direction
    ///   `towards`; among equal values it is closed when any of them is closed.
    /// - fails: returns [`IntervalError::Arithmetic`] when an exact product's
    ///   exponent overflows.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`IntervalError::Arithmetic`]: an exact product failed.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — operands that straddle zero on both sides, with equal
    ///   crossed products, held to the oracle.
    /// - witness: `tests::oracle::interval_product_encloses_every_product`
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |candidate| candidate.closure == Closure::Open || matches!(candidate.value, Corner::Finite(_))))]
    fn extreme(
        &self,
        other: &Self,
        corners: Corners,
        towards: Ordering,
    ) -> Result<Candidate, IntervalError>
    {
        let operands = [self, other];
        return match corners {
            Corners::One(left, right) => {
                Candidate::of(self.bound(left), other.bound(right), operands)
            },
            Corners::Two([(first_left, first_right), (second_left, second_right)]) => {
                let first =
                    Candidate::of(self.bound(first_left), other.bound(first_right), operands)?;
                let second =
                    Candidate::of(self.bound(second_left), other.bound(second_right), operands)?;
                Ok(match second.value.compare(&first.value) {
                    order if order == towards => second,
                    Ordering::Equal => {
                        let closure = if second.closure == Closure::Closed {
                            Closure::Closed
                        }
                        else {
                            first.closure
                        };
                        Candidate {
                            value: first.value,
                            closure,
                        }
                    },
                    Ordering::Less | Ordering::Greater => first,
                })
            },
        };
    }
}

/// The order of an endpoint against a dyadic.
///
/// # Specification
/// - ensures: returns how `endpoint` lies against `value` on the extended line.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — both infinities and a finite endpoint on each side.
/// - witness: `tests::interval::containment_reads_each_closure`
#[spec(ensures: |ref result| match *endpoint { Endpoint::NegInf => *result == Ordering::Less, Endpoint::PosInf => *result == Ordering::Greater, Endpoint::Finite(_) => true })]
fn against(
    endpoint: &Endpoint,
    value: &Dyadic,
) -> Ordering
{
    return match *endpoint {
        Endpoint::NegInf => Ordering::Less,
        Endpoint::Finite(ref finite) => finite.cmp(value),
        Endpoint::PosInf => Ordering::Greater,
    };
}

/// The sign of an endpoint on the extended line.
///
/// # Specification
/// - ensures: an infinity has its own sign, and a dyadic its sign.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the product's sign classes, with endpoints at zero and at
///   both infinities, held to the oracle.
/// - witness: `tests::oracle::interval_product_encloses_every_product`
#[spec(ensures: |ref result| match *endpoint { Endpoint::NegInf => *result == Sign::Negative, Endpoint::PosInf => *result == Sign::Positive, Endpoint::Finite(ref value) => *result == value.sign() })]
fn endpoint_sign(endpoint: &Endpoint) -> Sign
{
    return match *endpoint {
        Endpoint::NegInf => Sign::Negative,
        Endpoint::Finite(ref value) => value.sign(),
        Endpoint::PosInf => Sign::Positive,
    };
}

/// Whether the second operand of an endpoint sum is added or subtracted.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Polarity
{
    /// The sum `x + y`.
    Keep,
    /// The difference `x - y`.
    Flip,
}

/// One end of an interval.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Side
{
    /// The lower bound.
    Lower,
    /// The upper bound.
    Upper,
}

/// The endpoint products that bound one end of a product: one pair of
/// sides, or two pairs whose extreme is taken.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Corners
{
    /// The product of the first operand's bound on one side and the second
    /// operand's bound on the other.
    One(Side, Side),
    /// Two such products, of which the extreme one counts.
    Two([(Side, Side); 2]),
}

/// Where an endpoint lies on the extended line, after a polarity applies.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Reach
{
    /// The negative infinity.
    Negative,
    /// A finite value.
    Finite,
    /// The positive infinity.
    Positive,
}

/// The sign class of a proper interval, which selects the endpoint products.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Class
{
    /// Every element is at or above zero.
    Positive,
    /// Every element is at or below zero.
    Negative,
    /// The interval holds elements on both sides of zero.
    Mixed,
}

/// The sum or the difference of two bounds on the extended line, rounded
/// toward `rounding`.
///
/// # Specification
/// - ensures: when an infinity takes part, the result is the open infinity in
///   the rounding's direction if either operand reaches it, and the other open
///   infinity otherwise. Two finite endpoints give their rounded sum or
///   difference, closed exactly when both bounds are closed and the rounding
///   was exact.
/// - fails: returns [`IntervalError::Arithmetic`] when the finite result's
///   exponent leaves its range.
/// - panics: none.
///
/// # Errors
/// - [`IntervalError::Arithmetic`]: the finite sum failed.
///
/// # Adequacy
/// - hypothesis: L2 — the oracle forms each endpoint sum exactly, with rays and
///   both closures generated.
/// - witness: `tests::oracle::interval_sum_and_difference_round_outward`
#[spec(ensures: |ref result| result.as_ref().map_or(true, |bound| bound.closure == Closure::Open || matches!(bound.endpoint, Endpoint::Finite(_))))]
fn extended_sum(
    left: &Bound,
    right: &Bound,
    polarity: Polarity,
    precision: Precision,
    rounding: Rounding,
) -> Result<Bound, IntervalError>
{
    let (x, y) = match (&left.endpoint, &right.endpoint) {
        (&Endpoint::Finite(ref x), &Endpoint::Finite(ref y)) => (x, y),
        (&(Endpoint::NegInf | Endpoint::PosInf), _)
        | (_, &(Endpoint::NegInf | Endpoint::PosInf)) => {
            // An infinity in the rounding's direction bounds the result
            // soundly, so it wins over the other one.
            let toward = match rounding {
                Rounding::Floor => Reach::Negative,
                Rounding::Ceiling => Reach::Positive,
            };
            let reaches = reach(&left.endpoint, Polarity::Keep) == toward
                || reach(&right.endpoint, polarity) == toward;
            let infinity = match (reaches, rounding) {
                (true, Rounding::Floor) | (false, Rounding::Ceiling) => Endpoint::NegInf,
                (true, Rounding::Ceiling) | (false, Rounding::Floor) => Endpoint::PosInf,
            };
            return Ok(Bound::open(infinity));
        },
    };
    let rounded = match polarity {
        Polarity::Keep => x.add(y, precision, rounding)?,
        Polarity::Flip => x.sub(y, precision, rounding)?,
    };
    let closure = if left.closure == Closure::Closed
        && right.closure == Closure::Closed
        && rounded.exactness() == Exactness::Exact
    {
        Closure::Closed
    }
    else {
        Closure::Open
    };
    return Ok(Bound::new(Endpoint::Finite(rounded.into_value()), closure));
}

/// Where an endpoint lies on the extended line after `polarity` applies.
///
/// # Specification
/// - ensures: the side of an infinite endpoint, flipped under
///   [`Polarity::Flip`], and [`Reach::Finite`] for a finite endpoint.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — rays on each side of a difference, held to the oracle.
/// - witness: `tests::oracle::interval_sum_and_difference_round_outward`
#[spec(ensures: |ref result| (*result == Reach::Finite) == matches!(*endpoint, Endpoint::Finite(_)))]
fn reach(
    endpoint: &Endpoint,
    polarity: Polarity,
) -> Reach
{
    return match (endpoint, polarity) {
        (&Endpoint::NegInf, Polarity::Keep) | (&Endpoint::PosInf, Polarity::Flip) => {
            Reach::Negative
        },
        (&Endpoint::PosInf, Polarity::Keep) | (&Endpoint::NegInf, Polarity::Flip) => {
            Reach::Positive
        },
        (&Endpoint::Finite(_), Polarity::Keep | Polarity::Flip) => Reach::Finite,
    };
}

/// An exact endpoint product on the extended line, before rounding.
#[derive(Clone, Debug)]
enum Corner
{
    /// The negative infinity.
    NegInf,
    /// An exact finite product.
    Finite(Unrounded),
    /// The positive infinity.
    PosInf,
}

impl Corner
{
    /// The order of two corners on the extended line.
    ///
    /// # Specification
    /// - ensures: orders the two values, the infinities outermost.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the product's extremes, held to the oracle.
    /// - witness: `tests::oracle::interval_product_encloses_every_product`
    #[spec(ensures: |ref result| !matches!((self, other), (&Self::NegInf, &Self::NegInf) | (&Self::PosInf, &Self::PosInf)) || *result == Ordering::Equal)]
    fn compare(
        &self,
        other: &Self,
    ) -> Ordering
    {
        return match (self, other) {
            (&Self::NegInf, &Self::NegInf) | (&Self::PosInf, &Self::PosInf) => Ordering::Equal,
            (&Self::NegInf, &(Self::Finite(_) | Self::PosInf))
            | (&Self::Finite(_), &Self::PosInf) => Ordering::Less,
            (&(Self::Finite(_) | Self::PosInf), &Self::NegInf)
            | (&Self::PosInf, &Self::Finite(_)) => Ordering::Greater,
            (&Self::Finite(ref left), &Self::Finite(ref right)) => left.compare(right),
        };
    }
}

/// A candidate endpoint of a product: an exact corner and whether some pair
/// of elements attains it.
#[derive(Clone, Debug)]
struct Candidate
{
    /// The exact corner value.
    value: Corner,
    /// Closed when some pair of elements attains the value.
    closure: Closure,
}

impl Candidate
{
    /// The product of two bounds as a candidate endpoint.
    ///
    /// # Specification
    /// - ensures: the value is the exact product, zero for zero times an
    ///   infinity, and a signed infinity otherwise when an endpoint is
    ///   infinite. A finite value is attained when both bounds are closed, or
    ///   when it is zero and one of the two `operands` contains zero, which is
    ///   read only for a zero value.
    /// - fails: returns [`IntervalError::Arithmetic`] when the exact product's
    ///   exponent overflows.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`IntervalError::Arithmetic`]: the exact product failed.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero against an infinity, closed and open, with and
    ///   without zero in the other operand; L2 — the oracle's corners.
    /// - witness: `tests::interval::product_attains_zero_only_through_an_operand`
    /// - witness: `tests::oracle::interval_product_encloses_every_product`
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |candidate| candidate.closure == Closure::Open || matches!(candidate.value, Corner::Finite(_))))]
    fn of(
        left: &Bound,
        right: &Bound,
        operands: [&NumericInterval; 2],
    ) -> Result<Self, IntervalError>
    {
        let value = match (&left.endpoint, &right.endpoint) {
            (&Endpoint::Finite(ref x), &Endpoint::Finite(ref y)) => {
                Corner::Finite(x.exact_product(y)?)
            },
            (&Endpoint::Finite(ref finite), &Endpoint::NegInf)
            | (&Endpoint::NegInf, &Endpoint::Finite(ref finite)) => {
                scaled_infinity(finite.sign(), Infinity::Negative)
            },
            (&Endpoint::Finite(ref finite), &Endpoint::PosInf)
            | (&Endpoint::PosInf, &Endpoint::Finite(ref finite)) => {
                scaled_infinity(finite.sign(), Infinity::Positive)
            },
            (&Endpoint::NegInf, &Endpoint::NegInf) | (&Endpoint::PosInf, &Endpoint::PosInf) => {
                Corner::PosInf
            },
            (&Endpoint::NegInf, &Endpoint::PosInf) | (&Endpoint::PosInf, &Endpoint::NegInf) => {
                Corner::NegInf
            },
        };
        let closure = match value {
            Corner::Finite(ref exact) => {
                let both_closed =
                    left.closure == Closure::Closed && right.closure == Closure::Closed;
                let zero_attained = exact.sign() == Sign::Zero
                    && operands
                        .iter()
                        .any(|operand| operand.contains(&Dyadic::ZERO) == Containment::Contains);
                if both_closed || zero_attained {
                    Closure::Closed
                }
                else {
                    Closure::Open
                }
            },
            Corner::NegInf | Corner::PosInf => Closure::Open,
        };
        return Ok(Self { value, closure });
    }

    /// The candidate rounded to a bound toward `rounding`.
    ///
    /// # Specification
    /// - ensures: an infinite candidate is an open infinite bound. A finite
    ///   candidate rounds toward `rounding`, and the bound is closed exactly
    ///   when the candidate is attained and the rounding was exact.
    /// - fails: returns [`IntervalError::Arithmetic`] when the rounded exponent
    ///   leaves its range.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`IntervalError::Arithmetic`]: the rounding failed.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the product's endpoints and closures, held to the
    ///   oracle at narrow precisions where the rounding is inexact.
    /// - witness: `tests::oracle::interval_product_encloses_every_product`
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |bound| bound.closure == Closure::Open || matches!(bound.endpoint, Endpoint::Finite(_))))]
    fn rounded(
        self,
        precision: Precision,
        rounding: Rounding,
    ) -> Result<Bound, IntervalError>
    {
        return match self.value {
            Corner::NegInf => Ok(Bound::open(Endpoint::NegInf)),
            Corner::PosInf => Ok(Bound::open(Endpoint::PosInf)),
            Corner::Finite(exact) => {
                let rounded = exact.round(precision, rounding)?;
                let closure =
                    if self.closure == Closure::Closed && rounded.exactness() == Exactness::Exact {
                        Closure::Closed
                    }
                    else {
                        Closure::Open
                    };
                Ok(Bound::new(Endpoint::Finite(rounded.into_value()), closure))
            },
        };
    }
}

/// The product of a finite value of `sign` and an infinity; zero times an
/// infinity is zero.
///
/// # Specification
/// - ensures: zero for [`Sign::Zero`]; otherwise the infinity whose sign is the
///   product of the two signs.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — each sign against each infinity.
/// - witness: `tests::interval::product_attains_zero_only_through_an_operand`
#[spec(ensures: |ref result| matches!(*result, Corner::Finite(_)) == (sign == Sign::Zero))]
fn scaled_infinity(
    sign: Sign,
    infinity: Infinity,
) -> Corner
{
    return match (sign, infinity) {
        (Sign::Zero, Infinity::Negative | Infinity::Positive) => Corner::Finite(Unrounded::zero()),
        (Sign::Positive, Infinity::Positive) | (Sign::Negative, Infinity::Negative) => {
            Corner::PosInf
        },
        (Sign::Positive, Infinity::Negative) | (Sign::Negative, Infinity::Positive) => {
            Corner::NegInf
        },
    };
}

/// The sign of an infinite endpoint.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Infinity
{
    /// The negative infinity.
    Negative,
    /// The positive infinity.
    Positive,
}
