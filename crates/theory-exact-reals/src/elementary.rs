//! The builtin elementary functions: π, the cosine, the sine and the angle of
//! a point, each enclosed with dyadic endpoints.
//!
//! A plan over the field operations, a cut and the bounded quantifiers
//! defines only algebraic reals, so no such plan holds π. Each function here
//! is a node of its own, with one enclosure rule. The approximation pass and
//! the checker both read the rule. It sums an alternating series with
//! directed rounding, and the next term of the series bounds its remainder.
//!
//! # Boundaries
//!
//! |Function|Series|Reduction|
//! |---|---|---|
//! |π|`16 atan(1/5) − 4 atan(1/239)`, the formula of Machin|none|
//! |`cos x`, `sin x`|the Taylor series at the reduced point, with the Lagrange remainder|the nearest multiple of 2π|
//! |`arg x y`|`atan t` for `t` at most `1/2`|the octant of the point, and `atan t = π/4 − atan((1 − t)/(1 + t))` above `1/2`|
//!
//! The precision of a rule counts absolute bits: the enclosure at precision
//! `p` is at most about `5 · 2^-p` wide. Each term rounds at `p + 64`
//! significant bits, toward the floor for a lower bound and toward the
//! ceiling for an upper bound, so each bound is sound with no error analysis.
//! The π of a reduction holds 24 bits more, so a reduction of an argument
//! below `2^16` loses no bit of the rule. An argument at or past `2^16` in
//! magnitude gives the whole range `[−1, 1]`.
//!
//! The enclosure of a function over an interval is the exact range of the
//! function over it, enclosed tightly and then widened by `2 · 2^-p`. The
//! cosine and the sine take their extremes at the ends of the interval or at
//! a critical point inside it. The angle takes its extremes at the corners of
//! a box that holds no origin and crosses no negative axis. An exact range
//! over a smaller interval lies inside the range over a larger one. So an
//! enclosure at a finer precision, over the enclosure of a finer argument,
//! lies inside the coarser enclosure.
//!
//! The angle of a box that may hold the origin, or that may cross the
//! negative axis, is the whole circle. The angle of the point `(0, 0)` is
//! `0`.

use core::ops::Neg as _;

use num_bigint::BigInt;

use crate::certificate::CertificateCheck;
use crate::dyadic::BitWidth;
use crate::dyadic::Dyadic;
use crate::dyadic::Exponent;
use crate::dyadic::Precision;
use crate::dyadic::Rounding;
use crate::dyadic::Sign;
use crate::interval::Bound;
use crate::interval::Endpoint;
use crate::interval::NumericInterval;
use crate::interval::Orientation;
use crate::schema::exact;
use crate::schema::midpoint;

/// The bits that each term rounds at past the precision of the rule.
const GUARD: u32 = 64;

/// The bits past the precision of the rule at which a series stops.
const TAIL: u32 = 8;

/// The bits that the π of a reduction holds past the precision of the rule.
const REDUCTION: u32 = 24;

/// The exponent of the smallest magnitude of an argument that the cosine and
/// the sine reduce no more.
const FAR: i32 = 16;

/// The width that a step at `precision` needs, which the checker's width
/// quota bounds.
///
/// # Specification
/// - ensures: `precision + 88` bits: the working digits of the π of a
///   reduction.
/// - panics: none.
/// - executable: none — the clause restates the sum.
///
/// # Adequacy
/// - hypothesis: L3 — a step at the width quota and one past it.
/// - witness: `tests::elementary::a_step_past_the_width_quota_is_refused`
pub(crate) fn width(precision: Precision) -> BitWidth
{
    return BitWidth::from(
        u64::from(u32::from(precision)).saturating_add(u64::from(GUARD.saturating_add(REDUCTION))),
    );
}

/// The lower and the upper bound of a value.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct Pair
{
    /// The lower bound.
    lower: Dyadic,
    /// The upper bound.
    upper: Dyadic,
}

impl Pair
{
    /// The pair of `value` and `value`.
    ///
    /// # Specification
    /// trivial.
    fn point(value: &Dyadic) -> Self
    {
        return Self {
            lower: value.clone(),
            upper: value.clone(),
        };
    }
}

/// A count of series terms.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
struct Index(u32);

/// A quarter turn: the shift of the cosine that gives the sine.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Quarter
{
    /// The cosine itself.
    None,
    /// `cos (x − π/2)`, the sine.
    One,
}

/// The working precision of one rule.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct Work
{
    /// The absolute bits of the rule.
    bits: Precision,
    /// The significant bits that each term rounds at.
    digits: Precision,
    /// A series stops at its first term below `2^tail`.
    tail: Exponent,
    /// The most terms of one series.
    limit: Index,
}

impl Work
{
    /// The working precision of a rule at `precision`.
    ///
    /// # Specification
    /// - ensures: rounds at `precision + 64` significant bits, stops a series
    ///   below `2^-(precision + 8)`, and sums at most `4 · precision + 64`
    ///   terms.
    /// - fails: refuses a working precision past [`Precision::MAX`] as
    ///   [`CertificateCheck::WidthQuota`].
    /// - panics: none.
    /// - executable: none — the clause restates the fields.
    ///
    /// # Errors
    /// - [`CertificateCheck::WidthQuota`]: the working precision does not fit.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every rule reads it; the bench runs it at 64, 256 and
    ///   1024 bits.
    /// - witness: `tests::elementary::pi_holds_its_first_seventy_digits`
    fn at(precision: Precision) -> Result<Self, CertificateCheck>
    {
        let bits = u32::from(precision);
        let digits = Precision::try_from(bits.saturating_add(GUARD))
            .map_err(|_wide| CertificateCheck::WidthQuota)?;
        let tail = i32::try_from(bits.saturating_add(TAIL))
            .map_err(|_wide| CertificateCheck::WidthQuota)?;
        return Ok(Self {
            bits: precision,
            digits,
            tail: Exponent::from(tail.saturating_neg()),
            limit: Index(bits.saturating_mul(4).saturating_add(64)),
        });
    }

    /// The working precision of the π of a reduction at `precision`: 24 bits
    /// more.
    ///
    /// # Specification
    /// - ensures: as [`Self::at`], at `precision + 24`.
    /// - fails: as [`Self::at`].
    /// - panics: none.
    /// - executable: none — the clause restates the sum.
    ///
    /// # Errors
    /// As [`Self::at`].
    ///
    /// # Adequacy
    /// - hypothesis: L2 — points past several multiples of 2π against the
    ///   identities of the cosine and the sine.
    /// - witness: `tests::elementary::cosine_and_sine_meet_their_identities`
    fn reduction(precision: Precision) -> Result<Self, CertificateCheck>
    {
        let finer = Precision::try_from(u32::from(precision).saturating_add(REDUCTION))
            .map_err(|_wide| CertificateCheck::WidthQuota)?;
        return Self::at(finer);
    }
}

/// The dyadic `2^exponent`.
///
/// # Specification
/// trivial.
fn power_of_two(exponent: Exponent) -> Result<Dyadic, CertificateCheck>
{
    return Dyadic::new(BigInt::from(1_u8), exponent)
        .map_err(|_overflow| CertificateCheck::WidthQuota);
}

/// The dyadic integer `value`.
///
/// # Specification
/// trivial.
fn integer(value: BigInt) -> Result<Dyadic, CertificateCheck>
{
    return Dyadic::new(value, Exponent::from(0_i32))
        .map_err(|_overflow| CertificateCheck::WidthQuota);
}

/// The exact sum of `first` and `second`.
///
/// # Specification
/// trivial.
fn plus(
    first: &Dyadic,
    second: &Dyadic,
) -> Result<Dyadic, CertificateCheck>
{
    return exact(first.add(second, Precision::MAX, Rounding::Floor));
}

/// The exact difference of `first` and `second`.
///
/// # Specification
/// trivial.
fn minus(
    first: &Dyadic,
    second: &Dyadic,
) -> Result<Dyadic, CertificateCheck>
{
    return exact(first.sub(second, Precision::MAX, Rounding::Floor));
}

/// The exact product of `first` and `second`.
///
/// # Specification
/// trivial.
fn times(
    first: &Dyadic,
    second: &Dyadic,
) -> Result<Dyadic, CertificateCheck>
{
    return exact(first.mul(second, Precision::MAX, Rounding::Floor));
}

/// The magnitude of `value`.
///
/// # Specification
/// trivial.
fn magnitude(value: &Dyadic) -> Dyadic
{
    return match value.sign() {
        Sign::Negative => value.neg(),
        Sign::Zero | Sign::Positive => value.clone(),
    };
}

/// The nearest integer to `value`, the lower one at a half.
///
/// # Specification
/// - ensures: the floor of `value + 1/2`, an integer.
/// - fails: refuses an exponent past the range of [`Exponent`] as
///   [`CertificateCheck::WidthQuota`].
/// - panics: none.
/// - executable: none — the clause restates the rounding.
///
/// # Errors
/// - [`CertificateCheck::WidthQuota`]: an exponent overflows.
///
/// # Adequacy
/// - hypothesis: L3 — a reduction of a point past each multiple of 2π, of each
///   sign.
/// - witness: `tests::elementary::cosine_and_sine_meet_their_identities`
fn nearest(value: &Dyadic) -> Result<Dyadic, CertificateCheck>
{
    let half = power_of_two(Exponent::from(-1_i32))?;
    let shifted = plus(value, &half)?;
    // The floor or the ceiling on the grid of the integers: `top` significant
    // bits of a positive value whose highest bit is `top − 1`.
    let integral = |positive: &Dyadic, rounding: Rounding| -> Result<Dyadic, CertificateCheck> {
        let top = i64::from(i32::from(positive.exponent()))
            .saturating_add(i64::try_from(u64::from(positive.width())).unwrap_or(i64::MAX));
        if top <= 0 {
            return Ok(match rounding {
                Rounding::Floor => Dyadic::ZERO,
                Rounding::Ceiling => Dyadic::ONE,
            });
        }
        let bits = u32::try_from(top)
            .ok()
            .and_then(|bits| Precision::try_from(bits).ok())
            .ok_or(CertificateCheck::WidthQuota)?;
        return exact(positive.round(bits, rounding));
    };
    return match shifted.sign() {
        Sign::Zero => Ok(Dyadic::ZERO),
        Sign::Positive => integral(&shifted, Rounding::Floor),
        Sign::Negative => Ok(integral(&shifted.neg(), Rounding::Ceiling)?.neg()),
    };
}

/// The enclosure of the alternating series `t₀ − t₁ + t₂ − …`, from bounds on
/// its first term and a rule for each next term.
///
/// # Specification
/// - requires: each term lies at or above zero, and the magnitude of the tail
///   after the first `n` terms lies at or below the `n`-th term: the series
///   decreases, or its Lagrange remainder is that term.
/// - ensures: the partial sum up to the first term below `2^tail`, or up to the
///   limit of terms, widened by that term's upper bound. Each partial sum
///   rounds outward at the working digits.
/// - fails: as the rule of the next term fails, or as an exponent overflows.
/// - panics: none.
/// - executable: none — the requirement speaks of the series' limit.
/// - intension: one rounded addition and one call of `next` for each term.
///
/// # Errors
/// The [`CertificateCheck`] of `next`, or [`CertificateCheck::WidthQuota`].
///
/// # Adequacy
/// - hypothesis: L2 — π, the cosine, the sine and the angle against their
///   identities and their decimal digits.
/// - witness: `tests::elementary::pi_holds_its_first_seventy_digits`
/// - witness: `tests::elementary::cosine_and_sine_meet_their_identities`
fn alternating<Next>(
    work: &Work,
    first: Pair,
    mut next: Next,
) -> Result<Pair, CertificateCheck>
where
    Next: FnMut(&Pair, Index) -> Result<Pair, CertificateCheck>,
{
    let tail = power_of_two(work.tail)?;
    let mut sum = Pair::point(&Dyadic::ZERO);
    let mut term = first;
    let mut index = Index(0);
    while term.upper >= tail && index < work.limit {
        sum = if index.0 & 1 == 0 {
            Pair {
                lower: exact(sum.lower.add(&term.lower, work.digits, Rounding::Floor))?,
                upper: exact(sum.upper.add(&term.upper, work.digits, Rounding::Ceiling))?,
            }
        }
        else {
            Pair {
                lower: exact(sum.lower.sub(&term.upper, work.digits, Rounding::Floor))?,
                upper: exact(sum.upper.sub(&term.lower, work.digits, Rounding::Ceiling))?,
            }
        };
        term = next(&term, index)?;
        index = Index(index.0.saturating_add(1));
    }
    return Ok(Pair {
        lower: exact(sum.lower.sub(&term.upper, work.digits, Rounding::Floor))?,
        upper: exact(sum.upper.add(&term.upper, work.digits, Rounding::Ceiling))?,
    });
}

/// The term `term · factor / divisor`, rounded outward.
///
/// # Specification
/// trivial.
fn scaled(
    work: &Work,
    term: &Pair,
    factor: &Dyadic,
    divisor: &Dyadic,
) -> Result<Pair, CertificateCheck>
{
    let lower = exact(term.lower.mul(factor, work.digits, Rounding::Floor))?;
    let upper = exact(term.upper.mul(factor, work.digits, Rounding::Ceiling))?;
    return Ok(Pair {
        lower: exact(lower.div(divisor, work.digits, Rounding::Floor))?,
        upper: exact(upper.div(divisor, work.digits, Rounding::Ceiling))?,
    });
}

/// The odd number `2n + 1` of the term `n`, as a dyadic integer.
///
/// # Specification
/// trivial.
fn odd(index: Index) -> Result<Dyadic, CertificateCheck>
{
    return integer(BigInt::from(
        u64::from(index.0).saturating_mul(2).saturating_add(1),
    ));
}

/// `atan (1/k)` for an integer `k` above one, by its series.
///
/// # Specification
/// - requires: `k` is at least 2, so the terms decrease.
/// - ensures: an enclosure of `atan (1/k)` within about `2^tail`.
/// - fails: as [`alternating`].
/// - panics: none.
/// - executable: none — the clause speaks of the arctangent.
///
/// # Errors
/// As [`alternating`].
///
/// # Adequacy
/// - hypothesis: L2 — through π, against its decimal digits.
/// - witness: `tests::elementary::pi_holds_its_first_seventy_digits`
fn arctangent_of_inverse(
    work: &Work,
    k: &Dyadic,
) -> Result<Pair, CertificateCheck>
{
    // The power `k^-(2n+1)` of the term `n`, rounded outward: each term
    // divides it by `k²`, a small integer.
    let square = times(k, k)?;
    let mut power = Pair {
        lower: exact(Dyadic::ONE.div(k, work.digits, Rounding::Floor))?,
        upper: exact(Dyadic::ONE.div(k, work.digits, Rounding::Ceiling))?,
    };
    let first = power.clone();
    return alternating(work, first, |_term, index| {
        power = Pair {
            lower: exact(power.lower.div(&square, work.digits, Rounding::Floor))?,
            upper: exact(power.upper.div(&square, work.digits, Rounding::Ceiling))?,
        };
        let divisor = odd(Index(index.0.saturating_add(1)))?;
        return Ok(Pair {
            lower: exact(power.lower.div(&divisor, work.digits, Rounding::Floor))?,
            upper: exact(power.upper.div(&divisor, work.digits, Rounding::Ceiling))?,
        });
    });
}

/// π, tightly: within about `2^tail`.
///
/// # Specification
/// - ensures: an enclosure of π by the formula of Machin.
/// - fails: as [`alternating`].
/// - panics: none.
/// - executable: none — the clause speaks of π.
///
/// # Errors
/// As [`alternating`].
///
/// # Adequacy
/// - hypothesis: L2 — against the decimal digits of π.
/// - witness: `tests::elementary::pi_holds_its_first_seventy_digits`
fn tight_pi(work: &Work) -> Result<Pair, CertificateCheck>
{
    let fifth = arctangent_of_inverse(work, &integer(BigInt::from(5_u8))?)?;
    let small = arctangent_of_inverse(work, &integer(BigInt::from(239_u8))?)?;
    let sixteen = integer(BigInt::from(16_u8))?;
    let four = integer(BigInt::from(4_u8))?;
    return Ok(Pair {
        lower: minus(
            &times(&sixteen, &fifth.lower)?,
            &times(&four, &small.upper)?,
        )?,
        upper: minus(
            &times(&sixteen, &fifth.upper)?,
            &times(&four, &small.lower)?,
        )?,
    });
}

/// The pair widened by `2^margin` on each side, and rounded outward at the
/// working digits.
///
/// # Specification
/// - ensures: the lower bound less the margin, rounded down, and the upper
///   bound plus the margin, rounded up.
/// - fails: refuses an exponent past its range as
///   [`CertificateCheck::WidthQuota`].
/// - panics: none.
/// - executable: none — the clause restates the arithmetic.
///
/// # Errors
/// - [`CertificateCheck::WidthQuota`]: an exponent overflows.
///
/// # Adequacy
/// - hypothesis: L2 — each rule at 64, 256 and 1024 bits lies inside the rule
///   at the coarser precision.
/// - witness: `tests::elementary::a_finer_precision_nests_inside_a_coarser_one`
fn widened(
    work: &Work,
    pair: &Pair,
    margin: Exponent,
) -> Result<Pair, CertificateCheck>
{
    let margin = power_of_two(margin)?;
    return Ok(Pair {
        lower: exact(pair.lower.sub(&margin, work.digits, Rounding::Floor))?,
        upper: exact(pair.upper.add(&margin, work.digits, Rounding::Ceiling))?,
    });
}

/// The exponent `offset − bits` of a margin of a rule.
///
/// # Specification
/// trivial.
fn margin(
    work: &Work,
    offset: Exponent,
) -> Result<Exponent, CertificateCheck>
{
    let bits = i32::try_from(u32::from(work.bits)).map_err(|_wide| CertificateCheck::WidthQuota)?;
    return Ok(Exponent::from(i32::from(offset).saturating_sub(bits)));
}

/// The closed interval of `pair`.
///
/// # Specification
/// trivial.
fn closed(pair: Pair) -> Result<NumericInterval, CertificateCheck>
{
    return NumericInterval::new(
        Bound::closed(pair.lower),
        Bound::closed(pair.upper),
        Orientation::Proper,
    )
    .map_err(|_reversed| CertificateCheck::OutsideEnclosure);
}

/// The enclosure of π at `precision`: a closed interval about `5 ·
/// 2^-precision` wide.
///
/// # Specification
/// - ensures: a closed interval that holds π, tight within `2^-(precision + 8)`
///   and widened by `2 · 2^-precision`. The interval at a finer precision lies
///   inside it.
/// - fails: refuses a working precision past its range as
///   [`CertificateCheck::WidthQuota`].
/// - panics: none.
/// - executable: none — the clause speaks of π.
/// - intension: about `(precision + 72) / 4.6` terms of `atan (1/5)` and a
///   quarter as many of `atan (1/239)`, each one rounded division.
///
/// # Errors
/// - [`CertificateCheck::WidthQuota`]: the working precision does not fit.
///
/// # Adequacy
/// - hypothesis: L2 — against the first 70 decimal digits of π, and nested
///   across 64, 256 and 1024 bits.
/// - witness: `tests::elementary::pi_holds_its_first_seventy_digits`
/// - witness: `tests::elementary::a_finer_precision_nests_inside_a_coarser_one`
#[inline]
pub fn pi(precision: Precision) -> Result<NumericInterval, CertificateCheck>
{
    let work = Work::at(precision)?;
    let tight = tight_pi(&work)?;
    return closed(widened(
        &work,
        &tight,
        margin(&work, Exponent::from(1_i32))?,
    )?);
}

/// The Taylor series of `cos c` or `sin c` at a point `c` within about π of
/// zero.
///
/// # Specification
/// - ensures: an enclosure of `cos c` for [`Quarter::None`], and of `sin c` for
///   [`Quarter::One`], within about `2^tail`.
/// - fails: as [`alternating`].
/// - panics: none.
/// - executable: none — the clause speaks of the cosine.
///
/// # Errors
/// As [`alternating`].
///
/// # Adequacy
/// - hypothesis: L2 — against the identities of the cosine and the sine.
/// - witness: `tests::elementary::cosine_and_sine_meet_their_identities`
fn taylor(
    work: &Work,
    c: &Dyadic,
    quarter: Quarter,
) -> Result<Pair, CertificateCheck>
{
    let square = times(c, c)?;
    let size = magnitude(c);
    let (first, shift) = match quarter {
        Quarter::None => (Pair::point(&Dyadic::ONE), 1_u64),
        Quarter::One => (Pair::point(&size), 2_u64),
    };
    let sum = alternating(work, first, |term, index| {
        // The term `n + 1` is the term `n` times `c²` over the next two
        // factors of the factorial.
        let base = u64::from(index.0).saturating_mul(2).saturating_add(shift);
        let divisor = times(
            &integer(BigInt::from(base))?,
            &integer(BigInt::from(base.saturating_add(1)))?,
        )?;
        return scaled(work, term, &square, &divisor);
    })?;
    return Ok(match (quarter, c.sign()) {
        (Quarter::One, Sign::Negative) => Pair {
            lower: sum.upper.neg(),
            upper: sum.lower.neg(),
        },
        (Quarter::None, Sign::Negative | Sign::Zero | Sign::Positive)
        | (Quarter::One, Sign::Zero | Sign::Positive) => sum,
    });
}

/// The cosine at the point `x` for [`Quarter::None`], or the sine for
/// [`Quarter::One`], tightly.
///
/// # Specification
/// - requires: `x` lies below `2^16` in magnitude, and `pi` holds 24 bits more
///   than the rule.
/// - ensures: an enclosure within about `2^tail`, the error of the reduction
///   included.
/// - fails: as [`alternating`].
/// - panics: none.
/// - executable: none — the clause speaks of the cosine.
///
/// # Errors
/// As [`alternating`].
///
/// # Adequacy
/// - hypothesis: L2 — points past several multiples of 2π, of each sign.
/// - witness: `tests::elementary::cosine_and_sine_meet_their_identities`
fn wave_at(
    work: &Work,
    x: &Dyadic,
    quarter: Quarter,
    pi: &Pair,
) -> Result<Pair, CertificateCheck>
{
    let half = power_of_two(Exponent::from(-1_i32))?;
    let two = integer(BigInt::from(2_u8))?;
    let turn = Pair {
        lower: times(&two, &pi.lower)?,
        upper: times(&two, &pi.upper)?,
    };
    let turns = nearest(&exact(x.div(&turn.lower, work.digits, Rounding::Floor))?)?;
    // The reduced interval `x − turns · 2π`, its ends rounded outward by the
    // sign of the turns.
    let (near, far) = match turns.sign() {
        Sign::Negative => (&turn.lower, &turn.upper),
        Sign::Zero | Sign::Positive => (&turn.upper, &turn.lower),
    };
    let reduced = Pair {
        lower: minus(x, &times(&turns, near)?)?,
        upper: minus(x, &times(&turns, far)?)?,
    };
    let point = midpoint(&reduced.lower, &reduced.upper)?;
    let radius = times(&minus(&reduced.upper, &reduced.lower)?, &half)?;
    // The cosine and the sine are 1-Lipschitz, so the radius of the reduced
    // interval widens the series at its midpoint.
    let series = taylor(work, &point, quarter)?;
    return Ok(Pair {
        lower: exact(series.lower.sub(&radius, work.digits, Rounding::Floor))?,
        upper: exact(series.upper.add(&radius, work.digits, Rounding::Ceiling))?,
    });
}

/// The closed ends of a finite proper interval, or `None`.
///
/// # Specification
/// trivial.
fn ends(interval: &NumericInterval) -> Option<(Dyadic, Dyadic)>
{
    if interval.orientation() != Orientation::Proper {
        return None;
    }
    return match (&interval.lower().endpoint, &interval.upper().endpoint) {
        (&Endpoint::Finite(ref lower), &Endpoint::Finite(ref upper)) => {
            Some((lower.clone(), upper.clone()))
        },
        (&(Endpoint::NegInf | Endpoint::Finite(_) | Endpoint::PosInf), _) => None,
    };
}

/// The enclosure of `cos (x − q · π/2)` over the argument at `precision`.
///
/// # Specification
/// - ensures: as [`cosine`], for the shift `q`.
/// - fails: as [`cosine`].
/// - panics: none.
/// - executable: none — the clause speaks of the cosine.
///
/// # Errors
/// As [`cosine`].
///
/// # Adequacy
/// - hypothesis: L2 — as [`cosine`] and [`sine`].
/// - witness: `tests::elementary::cosine_and_sine_meet_their_identities`
/// - witness: `tests::elementary::a_finer_precision_nests_inside_a_coarser_one`
fn wave(
    argument: &NumericInterval,
    precision: Precision,
    quarter: Quarter,
) -> Result<NumericInterval, CertificateCheck>
{
    let unit = Pair {
        lower: Dyadic::ONE.neg(),
        upper: Dyadic::ONE,
    };
    let Some((lower, upper)) = ends(argument)
    else {
        return closed(unit);
    };
    let far = power_of_two(Exponent::from(FAR))?;
    if magnitude(&lower) >= far || magnitude(&upper) >= far {
        return closed(unit);
    }
    let work = Work::at(precision)?;
    let pi = tight_pi(&Work::reduction(precision)?)?;
    let turn = times(&integer(BigInt::from(2_u8))?, &pi.lower)?;
    if minus(&upper, &lower)? >= turn {
        return closed(unit);
    }
    let first = wave_at(&work, &lower, quarter, &pi)?;
    let second = if upper == lower {
        first.clone()
    }
    else {
        wave_at(&work, &upper, quarter, &pi)?
    };
    let mut range = Pair {
        lower: core::cmp::min(first.lower, second.lower),
        upper: core::cmp::max(first.upper, second.upper),
    };
    // The critical points of `cos (x − q · π/2)` are `(j + q/2) · π`: a
    // maximum for an even `j`, a minimum for an odd one. The interval is
    // shorter than 2π, so five candidates from the one below its lower end
    // cover it.
    let offset = match quarter {
        Quarter::None => Dyadic::ZERO,
        Quarter::One => power_of_two(Exponent::from(-1_i32))?,
    };
    let ratio = exact(lower.div(&pi.lower, work.digits, Rounding::Floor))?;
    let mut candidate = minus(&nearest(&minus(&ratio, &offset)?)?, &Dyadic::ONE)?;
    for _ in 0_u8 .. 5_u8 {
        let factor = plus(&candidate, &offset)?;
        let (near, far) = match factor.sign() {
            Sign::Negative => (&pi.upper, &pi.lower),
            Sign::Zero | Sign::Positive => (&pi.lower, &pi.upper),
        };
        let critical = Pair {
            lower: times(&factor, near)?,
            upper: times(&factor, far)?,
        };
        if critical.lower <= upper && critical.upper >= lower {
            let even = candidate == Dyadic::ZERO || i32::from(candidate.exponent()) > 0_i32;
            if even {
                range.upper = Dyadic::ONE;
            }
            else {
                range.lower = Dyadic::ONE.neg();
            }
        }
        candidate = plus(&candidate, &Dyadic::ONE)?;
    }
    let wide = widened(&work, &range, margin(&work, Exponent::from(1_i32))?)?;
    return closed(Pair {
        lower: core::cmp::max(wide.lower, unit.lower),
        upper: core::cmp::min(wide.upper, unit.upper),
    });
}

/// The enclosure of the cosine over the argument at `precision`.
///
/// # Specification
/// - ensures: a closed interval inside `[−1, 1]` that holds `cos x` for each
///   `x` of the argument. It is the exact range, tight within about
///   `2^-(precision + 8)` and widened by `2 · 2^-precision`. An argument that
///   is unbounded, dual, at least 2π wide, or at or past `2^16` in magnitude
///   gives `[−1, 1]`.
/// - fails: refuses a working precision past its range as
///   [`CertificateCheck::WidthQuota`].
/// - panics: none.
/// - executable: none — the clause speaks of the cosine.
/// - intension: one series at each end of the argument, one for a point, and π
///   once.
///
/// # Errors
/// - [`CertificateCheck::WidthQuota`]: the working precision does not fit.
///
/// # Adequacy
/// - hypothesis: L2 — against `cos (π/4)`, `cos² + sin² = 1` and nesting across
///   precisions.
/// - witness: `tests::elementary::cosine_and_sine_meet_their_identities`
/// - witness: `tests::elementary::a_finer_precision_nests_inside_a_coarser_one`
#[inline]
pub fn cosine(
    argument: &NumericInterval,
    precision: Precision,
) -> Result<NumericInterval, CertificateCheck>
{
    return wave(argument, precision, Quarter::None);
}

/// The enclosure of the sine over the argument at `precision`.
///
/// # Specification
/// - ensures: as [`cosine`], for the sine.
/// - fails: as [`cosine`].
/// - panics: none.
/// - executable: none — the clause speaks of the sine.
///
/// # Errors
/// As [`cosine`].
///
/// # Adequacy
/// - hypothesis: L2 — against `sin (π/6)`, `cos² + sin² = 1` and nesting across
///   precisions.
/// - witness: `tests::elementary::cosine_and_sine_meet_their_identities`
/// - witness: `tests::elementary::a_finer_precision_nests_inside_a_coarser_one`
#[inline]
pub fn sine(
    argument: &NumericInterval,
    precision: Precision,
) -> Result<NumericInterval, CertificateCheck>
{
    return wave(argument, precision, Quarter::One);
}

/// `atan t` over an interval `t` from 0 to 1, tightly.
///
/// # Specification
/// - requires: `t` lies from 0 to 1.
/// - ensures: an enclosure within about `2^tail` of `atan` over `t`, by the
///   series over `t` when `t` lies at most `1/2`, and by `π/4 − atan ((1 −
///   t)/(1 + t))` else.
/// - fails: as [`alternating`].
/// - panics: none.
/// - executable: none — the clause speaks of the arctangent.
/// - intension: one series.
///
/// # Errors
/// As [`alternating`].
///
/// # Adequacy
/// - hypothesis: L2 — angles of the points of each octant against π.
/// - witness: `tests::elementary::angles_of_the_octants_and_the_origin`
fn arctangent_at(
    work: &Work,
    t: &Pair,
    pi: &Pair,
) -> Result<Pair, CertificateCheck>
{
    let half = power_of_two(Exponent::from(-1_i32))?;
    // Each term `u^(2n+1)/(2n+1)` rises with `u`, so the lower ends of the
    // terms come from the lower end of `u`, and the upper ends from its upper
    // end.
    let series = |u: &Pair| -> Result<Pair, CertificateCheck> {
        let square = Pair {
            lower: exact(u.lower.mul(&u.lower, work.digits, Rounding::Floor))?,
            upper: exact(u.upper.mul(&u.upper, work.digits, Rounding::Ceiling))?,
        };
        let mut power = u.clone();
        return alternating(work, u.clone(), |_term, index| {
            power = Pair {
                lower: exact(power.lower.mul(&square.lower, work.digits, Rounding::Floor))?,
                upper: exact(
                    power
                        .upper
                        .mul(&square.upper, work.digits, Rounding::Ceiling),
                )?,
            };
            let divisor = odd(Index(index.0.saturating_add(1)))?;
            return Ok(Pair {
                lower: exact(power.lower.div(&divisor, work.digits, Rounding::Floor))?,
                upper: exact(power.upper.div(&divisor, work.digits, Rounding::Ceiling))?,
            });
        });
    };
    if t.upper <= half {
        return series(t);
    }
    // `(1 − t)/(1 + t)` falls as `t` rises, and it lies at most about `1/3`.
    let reflected = |end: &Dyadic, rounding: Rounding| {
        let numerator = minus(&Dyadic::ONE, end)?;
        let denominator = plus(&Dyadic::ONE, end)?;
        return exact(numerator.div(&denominator, work.digits, rounding));
    };
    let tail = series(&Pair {
        lower: reflected(&t.upper, Rounding::Floor)?,
        upper: reflected(&t.lower, Rounding::Ceiling)?,
    })?;
    let quarter = power_of_two(Exponent::from(-2_i32))?;
    return Ok(Pair {
        lower: minus(&times(&pi.lower, &quarter)?, &tail.upper)?,
        upper: minus(&times(&pi.upper, &quarter)?, &tail.lower)?,
    });
}

/// The angle of the point `(x, y)`, tightly, from `−π` to `π`.
///
/// # Specification
/// - ensures: an enclosure within about `2^tail` of the angle of the point, `0`
///   at the origin and `π` on the negative axis.
/// - fails: as [`alternating`].
/// - panics: none.
/// - executable: none — the clause speaks of the angle.
///
/// # Errors
/// As [`alternating`].
///
/// # Adequacy
/// - hypothesis: L2 — points of each octant and of each axis.
/// - witness: `tests::elementary::angles_of_the_octants_and_the_origin`
fn angle_at(
    work: &Work,
    (x, y): (&Dyadic, &Dyadic),
    pi: &Pair,
) -> Result<Pair, CertificateCheck>
{
    if *x == Dyadic::ZERO && *y == Dyadic::ZERO {
        return Ok(Pair::point(&Dyadic::ZERO));
    }
    let (across, up) = (magnitude(x), magnitude(y));
    let half = power_of_two(Exponent::from(-1_i32))?;
    // The ratio of the shorter side to the longer, rounded outward, and the
    // angle of `(|x|, |y|)` from it, from 0 to π/2.
    let ratio = |short: &Dyadic, long: &Dyadic| -> Result<Pair, CertificateCheck> {
        return Ok(Pair {
            lower: exact(short.div(long, work.digits, Rounding::Floor))?,
            upper: exact(short.div(long, work.digits, Rounding::Ceiling))?,
        });
    };
    let base = if up <= across {
        arctangent_at(work, &ratio(&up, &across)?, pi)?
    }
    else {
        let steep = arctangent_at(work, &ratio(&across, &up)?, pi)?;
        Pair {
            lower: minus(&times(&pi.lower, &half)?, &steep.upper)?,
            upper: minus(&times(&pi.upper, &half)?, &steep.lower)?,
        }
    };
    let left = x.sign() == Sign::Negative;
    let below = y.sign() == Sign::Negative;
    return Ok(match (left, below) {
        (false, false) => base,
        (true, false) => Pair {
            lower: minus(&pi.lower, &base.upper)?,
            upper: minus(&pi.upper, &base.lower)?,
        },
        (true, true) => Pair {
            lower: minus(&base.lower, &pi.upper)?,
            upper: minus(&base.upper, &pi.lower)?,
        },
        (false, true) => Pair {
            lower: base.upper.neg(),
            upper: base.lower.neg(),
        },
    });
}

/// The enclosure of the angle of the point `(x, y)` over a box at
/// `precision`.
///
/// # Specification
/// - ensures: a closed interval that holds the angle, from `−π` to `π`, of each
///   point of the box. The box of the origin alone gives `[0, 0]`. A box that
///   holds the origin and another point, that may cross the negative axis, or
///   that is unbounded or dual gives the whole circle, widened by
///   `2^-precision`. Any other box gives the exact range of its corners, tight
///   within about `2^-(precision + 8)` and widened by `2 · 2^-precision`.
/// - fails: refuses a working precision past its range as
///   [`CertificateCheck::WidthQuota`].
/// - panics: none.
/// - executable: none — the clause speaks of the angle.
/// - intension: π once, and the angle of each distinct corner of the box, one
///   series each.
///
/// # Errors
/// - [`CertificateCheck::WidthQuota`]: the working precision does not fit.
///
/// # Adequacy
/// - hypothesis: L2 — points of each octant and axis, the origin, boxes that
///   hold it and boxes that cross the negative axis, nested across precisions.
/// - witness: `tests::elementary::angles_of_the_octants_and_the_origin`
/// - witness: `tests::elementary::a_finer_precision_nests_inside_a_coarser_one`
#[inline]
pub fn angle(
    x: &NumericInterval,
    y: &NumericInterval,
    precision: Precision,
) -> Result<NumericInterval, CertificateCheck>
{
    let work = Work::at(precision)?;
    let pi = tight_pi(&work)?;
    let bound = widened(&work, &pi, margin(&work, Exponent::from(0_i32))?)?.upper;
    let circle = closed(Pair {
        lower: bound.neg(),
        upper: bound.clone(),
    });
    let (Some((left, right)), Some((bottom, top))) = (ends(x), ends(y))
    else {
        return circle;
    };
    let zero = Dyadic::ZERO;
    if left <= zero && zero <= right && bottom <= zero && zero <= top {
        if left == zero && right == zero && bottom == zero && top == zero {
            return closed(Pair::point(&zero));
        }
        return circle;
    }
    if left < zero && bottom < zero && zero <= top {
        return circle;
    }
    // The extremes of the angle over a box that holds no origin and crosses no
    // negative axis lie at its corners. An interval of one point gives one
    // side, not two.
    let columns = [Some(&left), (left != right).then_some(&right)];
    let rows = [Some(&bottom), (bottom != top).then_some(&top)];
    let mut range: Option<Pair> = None;
    for column in columns.into_iter().flatten() {
        for row in rows.into_iter().flatten() {
            let at = angle_at(&work, (column, row), &pi)?;
            range = Some(match range {
                None => at,
                Some(known) => Pair {
                    lower: core::cmp::min(known.lower, at.lower),
                    upper: core::cmp::max(known.upper, at.upper),
                },
            });
        }
    }
    let range = range.ok_or(CertificateCheck::OutsideEnclosure)?;
    let wide = widened(&work, &range, margin(&work, Exponent::from(1_i32))?)?;
    return closed(Pair {
        lower: core::cmp::max(wide.lower, bound.neg()),
        upper: core::cmp::min(wide.upper, bound),
    });
}
