//! The recurrence rule: the enclosure of the sum of a series whose term ratio
//! is a rational function of the index, with dyadic endpoints.
//!
//! A plan over the field operations, a cut and the bounded quantifiers
//! defines only algebraic reals. A [`Recurrence`] node defines the sum of a
//! series instead. Its first term is one, and the term after `t_n` is
//! `t_n · a · p(n) / q(n)`. One rule serves `exp`, `log` and each later
//! function of that form, so such a function needs no rule of its own. The
//! approximation pass, the certificate writer and the checker all read this
//! rule.
//!
//! # Boundaries
//!
//! |Part|Rule|
//! |---|---|
//! |partial sum|`N` terms over the enclosure of the argument; each product and quotient rounds outward at `p + 64` significant bits, and the integer `p(n)` multiplies exactly|
//! |tail|`|t_N| / (1 − ρ)`, for an upper bound `ρ` on `|a · p(n) / q(n)|` at each `n ≥ N` (Johansson 2019, Theorem 1)|
//! |count `N`|the first term below `2^-(p + 8)` after which `ρ` lies below one, at most 65,536 terms|
//! |validation|the degree of `p` is at most the degree of `q`, and `q` has no root at a natural number|
//!
//! The bound `ρ` reads the coefficients alone. Let `d` be the degree of `q`.
//! For `n ≥ N ≥ 1`, `|p(n)|` is at most `Σ |p_i| n^i`, and `|q(n)|` is at
//! least `|q_d| n^d − Σ_{i<d} |q_i| n^i`. Each `n^(i−d)` is at most
//! `N^(i−d)`. So `ρ = |a| · Σ |p_i| N^(i−d) / (|q_d| − Σ_{i<d} |q_i| N^(i−d))`
//! holds, and the tail is at most a geometric series of ratio `ρ`. The bound
//! works at 32 significant bits, rounded upward, because it only widens the
//! enclosure.
//!
//! When the degrees are equal, the series converges only inside the radius
//! `|q_d / p_d|`. While the enclosure of the argument reaches past the
//! radius, `ρ` stays at or above one, and the rule refuses before it sums a
//! term. A finer enclosure of the argument can settle the node later, so the
//! convergence is a semidecision. A term that is exactly zero ends the
//! series with no tail.
//!
//! # References
//!
//! - `vault:01a1b53e-d768-7e62-8825-088be647563b` — exemplar: the source page
//!   of Fredrik Johansson, "Computing Hypergeometric Functions Rigorously", ACM
//!   Transactions on Mathematical Software 45(3), 2019, `doi:10.1145/3328732`.
//!   Its Theorem 1 in § 4.1 bounds the tail after `N` terms by `|t_N| / (1 −
//!   D)`, for a bound `D` on the term ratio at each index past `N`, and its
//!   remark computes `D` at a low precision rounded upward. The tail row above
//!   is that bound.

use core::ops::Add as _;
use core::ops::Mul as _;
use core::ops::Neg as _;

use num_bigint::BigInt;

use crate::certificate::CertificateCheck;
use crate::dyadic::Dyadic;
use crate::dyadic::Exponent;
use crate::dyadic::Precision;
use crate::dyadic::Rounding;
use crate::dyadic::Sign;
use crate::interval::Bound;
use crate::interval::Endpoint;
use crate::interval::NumericInterval;
use crate::interval::Orientation;
use crate::plan::Polynomial;
use crate::schema::exact;

/// The bits that each term rounds at past the precision of the rule.
const GUARD: u32 = 64;

/// The bits past the precision of the rule at which a series stops.
const TAIL: u32 = 8;

/// The significant bits of the tail bound.
const BOUND: u32 = 32;

/// The most terms of one series.
const TERMS: u32 = 1 << 16_u32;

/// A count of the terms of a series, or the index of one term.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Terms(u32);

impl Terms
{
    /// The most terms that one series sums: 65,536.
    pub const MAX: Self = Self(TERMS);
}

impl From<u32> for Terms
{
    /// The count `count`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: u32) -> Self
    {
        return Self(count);
    }
}

impl From<Terms> for u32
{
    /// The count as a number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(terms: Terms) -> Self
    {
        return terms.0;
    }
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

/// The sign class of a pair.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Class
{
    /// The lower bound lies at or above zero.
    Positive,
    /// The upper bound lies at or below zero.
    Negative,
    /// The pair holds zero inside.
    Mixed,
}

/// The working precision of one series.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct Work
{
    /// The significant bits that each term rounds at.
    digits: Precision,
    /// The significant bits of the tail bound.
    bound: Precision,
    /// The series stops at its first term below this magnitude.
    stop: Dyadic,
}

impl Work
{
    /// The working precision of a series at `precision`.
    ///
    /// # Specification
    /// - ensures: rounds each term at `precision + 64` significant bits, bounds
    ///   the tail at 32 bits, and stops below `2^-(precision + 8)`.
    /// - fails: refuses a working precision past [`Precision::MAX`] as
    ///   [`CertificateCheck::WidthQuota`].
    /// - panics: none.
    /// - executable: none — the clause restates the fields.
    ///
    /// # Errors
    /// - [`CertificateCheck::WidthQuota`]: the working precision does not fit.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — `exp 1` and `log 2` past 1000 bits, and the bench at
    ///   64, 256 and 1024 bits.
    /// - witness: `tests::recurrence::exp_of_one_encloses_e_and_its_certificate_replays`
    fn at(precision: Precision) -> Result<Self, CertificateCheck>
    {
        let bits = u32::from(precision);
        let digits = Precision::try_from(bits.saturating_add(GUARD))
            .map_err(|_wide| CertificateCheck::WidthQuota)?;
        let bound = Precision::try_from(BOUND).map_err(|_wide| CertificateCheck::WidthQuota)?;
        let tail = i32::try_from(bits.saturating_add(TAIL))
            .map_err(|_wide| CertificateCheck::WidthQuota)?;
        let stop = Dyadic::new(BigInt::from(1_u8), Exponent::from(tail.saturating_neg()))
            .map_err(|_overflow| CertificateCheck::WidthQuota)?;
        return Ok(Self {
            digits,
            bound,
            stop,
        });
    }
}

/// The state of a series after some of its terms: their sum, the next term,
/// and the count of terms summed.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct Partial
{
    /// The sum of the terms so far, rounded outward.
    sum: Pair,
    /// The next term, rounded outward.
    term: Pair,
    /// The count of terms in the sum.
    terms: Terms,
}

impl Partial
{
    /// The state before the first term: an empty sum and the term one.
    ///
    /// # Specification
    /// trivial.
    fn start() -> Self
    {
        return Self {
            sum: Pair::point(&Dyadic::ZERO),
            term: Pair::point(&Dyadic::ONE),
            terms: Terms(0),
        };
    }
}

/// Where a partial sum stops.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Until
{
    /// After this count of terms, the count of a certificate's step.
    Count(Terms),
    /// At the first term below the stop of the work, the rule of the writer.
    Small,
}

/// The sign class of `pair`.
///
/// # Specification
/// trivial.
fn class(pair: &Pair) -> Class
{
    if pair.lower.sign() != Sign::Negative {
        return Class::Positive;
    }
    if pair.upper.sign() != Sign::Positive {
        return Class::Negative;
    }
    return Class::Mixed;
}

/// The largest magnitude of a point of `pair`.
///
/// # Specification
/// trivial.
fn magnitude(pair: &Pair) -> Dyadic
{
    let size = |value: &Dyadic| match value.sign() {
        Sign::Negative => value.neg(),
        Sign::Zero | Sign::Positive => value.clone(),
    };
    return core::cmp::max(size(&pair.lower), size(&pair.upper));
}

/// The product of two pairs, rounded outward at the working digits.
///
/// # Specification
/// - ensures: a pair that holds `x · y` for each `x` of `first` and `y` of
///   `second`. The signs select two endpoint products, or four when both pairs
///   hold zero inside.
/// - fails: refuses an exponent past its range as
///   [`CertificateCheck::WidthQuota`].
/// - panics: none.
/// - executable: none — the clause speaks of every point of the pairs.
///
/// # Errors
/// - [`CertificateCheck::WidthQuota`]: an exponent overflows.
///
/// # Adequacy
/// - hypothesis: L2 — the series of `exp` at points of each sign against the
///   identity `exp x · exp (−x) = 1`.
/// - witness: `tests::recurrence::exp_meets_its_identity_at_each_sign`
fn product(
    work: &Work,
    first: &Pair,
    second: &Pair,
) -> Result<Pair, CertificateCheck>
{
    let corner = |left: &Dyadic, right: &Dyadic, rounding: Rounding| {
        return exact(left.mul(right, work.digits, rounding));
    };
    let ((low_left, low_right), (high_left, high_right)) = match (class(first), class(second)) {
        (Class::Positive, Class::Positive) => {
            ((&first.lower, &second.lower), (&first.upper, &second.upper))
        },
        (Class::Positive, Class::Negative) => {
            ((&first.upper, &second.lower), (&first.lower, &second.upper))
        },
        (Class::Positive, Class::Mixed) => {
            ((&first.upper, &second.lower), (&first.upper, &second.upper))
        },
        (Class::Negative, Class::Positive) => {
            ((&first.lower, &second.upper), (&first.upper, &second.lower))
        },
        (Class::Negative, Class::Negative) => {
            ((&first.upper, &second.upper), (&first.lower, &second.lower))
        },
        (Class::Negative, Class::Mixed) => {
            ((&first.lower, &second.upper), (&first.lower, &second.lower))
        },
        (Class::Mixed, Class::Positive) => {
            ((&first.lower, &second.upper), (&first.upper, &second.upper))
        },
        (Class::Mixed, Class::Negative) => {
            ((&first.upper, &second.lower), (&first.lower, &second.lower))
        },
        (Class::Mixed, Class::Mixed) => {
            let lower = core::cmp::min(
                corner(&first.lower, &second.upper, Rounding::Floor)?,
                corner(&first.upper, &second.lower, Rounding::Floor)?,
            );
            let upper = core::cmp::max(
                corner(&first.lower, &second.lower, Rounding::Ceiling)?,
                corner(&first.upper, &second.upper, Rounding::Ceiling)?,
            );
            return Ok(Pair { lower, upper });
        },
    };
    return Ok(Pair {
        lower: corner(low_left, low_right, Rounding::Floor)?,
        upper: corner(high_left, high_right, Rounding::Ceiling)?,
    });
}

/// The pair times the integer `factor`, exactly.
///
/// # Specification
/// trivial.
fn scaled(
    pair: &Pair,
    factor: &Dyadic,
) -> Result<Pair, CertificateCheck>
{
    let times = |value: &Dyadic| exact(value.mul(factor, Precision::MAX, Rounding::Floor));
    return Ok(match factor.sign() {
        Sign::Negative => Pair {
            lower: times(&pair.upper)?,
            upper: times(&pair.lower)?,
        },
        Sign::Zero | Sign::Positive => Pair {
            lower: times(&pair.lower)?,
            upper: times(&pair.upper)?,
        },
    });
}

/// The pair over the integer `divisor`, rounded outward at the working
/// digits.
///
/// # Specification
/// trivial.
fn divided(
    work: &Work,
    pair: &Pair,
    divisor: &Dyadic,
) -> Result<Pair, CertificateCheck>
{
    let over =
        |value: &Dyadic, rounding: Rounding| exact(value.div(divisor, work.digits, rounding));
    return Ok(match divisor.sign() {
        Sign::Negative => Pair {
            lower: over(&pair.upper, Rounding::Floor)?,
            upper: over(&pair.lower, Rounding::Ceiling)?,
        },
        Sign::Zero => return Err(CertificateCheck::Tail),
        Sign::Positive => Pair {
            lower: over(&pair.lower, Rounding::Floor)?,
            upper: over(&pair.upper, Rounding::Ceiling)?,
        },
    });
}

/// The value of `polynomial` at the index `index`, exactly.
///
/// # Specification
/// - requires: the index is at most [`Terms::MAX`], so the value fits 98 bits.
/// - ensures: the integer `Σ c_i · index^i` as a dyadic.
/// - fails: refuses a value past `i128` as [`CertificateCheck::WidthQuota`].
/// - panics: none.
/// - executable: none — the requirement bounds the index, not the value.
///
/// # Errors
/// - [`CertificateCheck::WidthQuota`]: the value does not fit `i128`.
///
/// # Adequacy
/// - hypothesis: L2 — the ratios of `exp` and `log` over every index of their
///   series.
/// - witness: `tests::recurrence::exp_of_one_encloses_e_and_its_certificate_replays`
fn value(
    polynomial: &Polynomial,
    index: Terms,
) -> Result<Dyadic, CertificateCheck>
{
    let point = i128::from(index.0);
    let horner = polynomial
        .coefficients()
        .iter()
        .rev()
        .try_fold(0_i128, |sum, &coefficient| {
            return sum
                .checked_mul(point)?
                .checked_add(i128::from(i32::from(coefficient)));
        })
        .ok_or(CertificateCheck::WidthQuota)?;
    return match i64::try_from(horner) {
        Ok(small) => Ok(Dyadic::from(small)),
        Err(_wide) => Dyadic::new(BigInt::from(horner), Exponent::from(0_i32))
            .map_err(|_overflow| CertificateCheck::WidthQuota),
    };
}

/// Add terms to `partial` until `until` holds, each at the working digits.
///
/// # Specification
/// - requires: `q` has no root at a natural number, as validation keeps.
/// - ensures: the partial sum of the first `N` terms and the term `t_N`, each
///   rounded outward. A count stops at its `N`. The writer's rule stops at the
///   first term below the stop of the work, and at 65,536 terms. A term that is
///   exactly zero stops either, since each later term is zero.
/// - fails: as [`product`] and [`value`], and refuses a zero value of `q` as
///   [`CertificateCheck::Tail`].
/// - panics: none.
/// - executable: none — the clause speaks of the series' terms.
/// - intension: one product with the argument, one exact product with `p(n)`
///   and one quotient by `q(n)` for each term.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L2 — `exp` and `log` against their identities and digits.
/// - witness: `tests::recurrence::exp_of_one_encloses_e_and_its_certificate_replays`
/// - witness: `tests::recurrence::log_of_two_encloses_its_digits_and_its_certificate_replays`
fn summed(
    work: &Work,
    argument: &Pair,
    (numerator, denominator): (&Polynomial, &Polynomial),
    partial: &mut Partial,
    until: Until,
) -> Result<(), CertificateCheck>
{
    loop {
        let more = match until {
            Until::Count(count) => partial.terms < count,
            Until::Small => partial.terms < Terms::MAX && magnitude(&partial.term) >= work.stop,
        };
        let zero = partial.term.lower == Dyadic::ZERO && partial.term.upper == Dyadic::ZERO;
        if !more || zero {
            return Ok(());
        }
        partial.sum = Pair {
            lower: exact(
                partial
                    .sum
                    .lower
                    .add(&partial.term.lower, work.digits, Rounding::Floor),
            )?,
            upper: exact(partial.sum.upper.add(
                &partial.term.upper,
                work.digits,
                Rounding::Ceiling,
            ))?,
        };
        let moved = product(work, &partial.term, argument)?;
        let factor = value(numerator, partial.terms)?;
        let moved = if factor == Dyadic::ONE {
            moved
        }
        else {
            scaled(&moved, &factor)?
        };
        partial.term = divided(work, &moved, &value(denominator, partial.terms)?)?;
        partial.terms = Terms(partial.terms.0.saturating_add(1));
    }
}

/// The enclosure of the series: the partial sum, widened by its tail bound.
///
/// # Specification
/// - requires: the degree of `p` is at most the degree of `q`, as validation
///   keeps.
/// - ensures: the partial sum widened by `|t_N| / (1 − ρ)` on each side, for
///   the bound `ρ` of the module. A zero term widens nothing.
/// - fails: refuses as [`CertificateCheck::Tail`] when no term is summed, when
///   `p` has the higher degree, or when `ρ` does not lie below one.
/// - panics: none.
/// - executable: none — the clause speaks of every later term.
/// - intension: one power of `1/N` and one product for each coefficient, at 32
///   bits.
///
/// # Errors
/// - [`CertificateCheck::Tail`]: no tail bound holds after the `N` terms.
/// - [`CertificateCheck::WidthQuota`]: an exponent overflows.
///
/// # Adequacy
/// - hypothesis: L3 — a step of too few terms is refused, and the writer's
///   count replays.
/// - witness: `tests::recurrence::a_step_with_no_tail_bound_is_refused_by_name`
fn bounded(
    work: &Work,
    argument: &Pair,
    (numerator, denominator): (&Polynomial, &Polynomial),
    partial: &Partial,
) -> Result<Pair, CertificateCheck>
{
    if partial.term.lower == Dyadic::ZERO && partial.term.upper == Dyadic::ZERO {
        return Ok(partial.sum.clone());
    }
    let (over, under) = (numerator.coefficients(), denominator.coefficients());
    if partial.terms.0 == 0 || over.len() > under.len() {
        return Err(CertificateCheck::Tail);
    }
    let bits = work.bound;
    let up = |value: Result<crate::dyadic::Rounded, crate::dyadic::DyadicError>| exact(value);
    let inverse = up(Dyadic::ONE.div(
        &Dyadic::from(i64::from(partial.terms.0)),
        bits,
        Rounding::Ceiling,
    ))?;
    let degree = under.len().saturating_sub(1);
    // `N^(i − d)` for each `i` up to `d`, rounded upward.
    let mut powers = alloc::vec![Dyadic::ONE; degree.saturating_add(1)];
    for index in (0 .. degree).rev() {
        let above = powers
            .get(index.saturating_add(1))
            .cloned()
            .unwrap_or(Dyadic::ONE);
        let slot = powers.get_mut(index).ok_or(CertificateCheck::Tail)?;
        *slot = up(above.mul(&inverse, bits, Rounding::Ceiling))?;
    }
    let sized = |coefficient: i32, index: usize| -> Result<Dyadic, CertificateCheck> {
        let power = powers.get(index).ok_or(CertificateCheck::Tail)?;
        return up(Dyadic::from(i64::from(coefficient.unsigned_abs())).mul(
            power,
            bits,
            Rounding::Ceiling,
        ));
    };
    let mut top = Dyadic::ZERO;
    for (index, &coefficient) in over.iter().enumerate() {
        top = up(top.add(
            &sized(i32::from(coefficient), index)?,
            bits,
            Rounding::Ceiling,
        ))?;
    }
    let leading = under
        .last()
        .map_or(0_i32, |&coefficient| i32::from(coefficient));
    let mut bottom = Dyadic::from(i64::from(leading.unsigned_abs()));
    for (index, &coefficient) in under.iter().enumerate().take(degree) {
        bottom = up(bottom.sub(
            &sized(i32::from(coefficient), index)?,
            bits,
            Rounding::Floor,
        ))?;
    }
    if bottom.sign() != Sign::Positive {
        return Err(CertificateCheck::Tail);
    }
    let ratio = up(magnitude(argument).mul(&top, bits, Rounding::Ceiling))?;
    let ratio = up(ratio.div(&bottom, bits, Rounding::Ceiling))?;
    let gap = up(Dyadic::ONE.sub(&ratio, bits, Rounding::Floor))?;
    if gap.sign() != Sign::Positive {
        return Err(CertificateCheck::Tail);
    }
    let rest = up(magnitude(&partial.term).div(&gap, bits, Rounding::Ceiling))?;
    return Ok(Pair {
        lower: exact(partial.sum.lower.sub(&rest, work.digits, Rounding::Floor))?,
        upper: exact(partial.sum.upper.add(&rest, work.digits, Rounding::Ceiling))?,
    });
}

/// Refuse an argument whose enclosure reaches the radius of convergence, so
/// that no count bounds the tail.
///
/// # Specification
/// - ensures: succeeds unless the degrees of `p` and `q` are equal and `max |a|
///   · |p_d / q_d|`, rounded down, is at least one. Then `ρ` lies at or above
///   one at every count, because its numerator is at least `|p_d|` and its
///   denominator at most `|q_d|`.
/// - fails: refuses such an argument as [`CertificateCheck::Tail`].
/// - panics: none.
/// - executable: none — the clause speaks of every count.
/// - intension: one product and one quotient at 32 bits.
///
/// # Errors
/// - [`CertificateCheck::Tail`]: no count bounds the tail.
/// - [`CertificateCheck::WidthQuota`]: an exponent overflows.
///
/// # Adequacy
/// - hypothesis: L3 — the series of `log` at two, past its radius of one.
/// - witness: `tests::recurrence::a_step_with_no_tail_bound_is_refused_by_name`
fn radius(
    work: &Work,
    argument: &Pair,
    (numerator, denominator): (&Polynomial, &Polynomial),
) -> Result<(), CertificateCheck>
{
    let (over, under) = (numerator.coefficients(), denominator.coefficients());
    let (Some(&top), Some(&bottom)) = (over.last(), under.last())
    else {
        return Ok(());
    };
    if over.len() != under.len() {
        return Ok(());
    }
    let size = |coefficient: i32| Dyadic::from(i64::from(coefficient.unsigned_abs()));
    let limit = exact(magnitude(argument).mul(&size(i32::from(top)), work.bound, Rounding::Floor))?;
    let limit = exact(limit.div(&size(i32::from(bottom)), work.bound, Rounding::Floor))?;
    if limit >= Dyadic::ONE {
        return Err(CertificateCheck::Tail);
    }
    return Ok(());
}

/// The closed ends of a finite proper interval.
///
/// # Specification
/// trivial.
fn ends(interval: &NumericInterval) -> Result<Pair, CertificateCheck>
{
    if interval.orientation() != Orientation::Proper {
        return Err(CertificateCheck::Tail);
    }
    return match (&interval.lower().endpoint, &interval.upper().endpoint) {
        (&Endpoint::Finite(ref lower), &Endpoint::Finite(ref upper)) => Ok(Pair {
            lower: lower.clone(),
            upper: upper.clone(),
        }),
        (&(Endpoint::NegInf | Endpoint::Finite(_) | Endpoint::PosInf), _) => {
            Err(CertificateCheck::Tail)
        },
    };
}

/// The closed interval of a pair.
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
    .map_err(|_reversed| CertificateCheck::Tail);
}

/// The enclosure of the series of `ratio` over the argument at `precision`,
/// and the count of terms that it sums: the rule of the approximation pass
/// and of the certificate writer.
///
/// # Specification
/// - requires: the ratio is valid: the degree of `p` is at most the degree of
///   `q`, and `q` has no root at a natural number.
/// - ensures: a closed interval that holds the sum for each point of the
///   argument, and the count `N` that [`series_after`] takes to give the same
///   interval. `N` is the first count past the first term below
///   `2^-(precision+8)` at which the tail bound holds, and at most 65,536.
/// - fails: refuses as [`CertificateCheck::Tail`] when the argument is
///   unbounded or dual, or when no tail bound holds within 65,536 terms, and as
///   [`CertificateCheck::WidthQuota`] when the working precision does not fit.
/// - panics: none.
/// - executable: none — the clause speaks of the series' sum.
/// - intension: `N` terms, and one tail bound for each count past the first
///   small term until one holds.
///
/// # Errors
/// As above.
///
/// # Adequacy
/// - hypothesis: L2 — `exp 1`, `log 2` and `exp (log 3)` against `e`, the
///   digits of `log 2` and `3`; the generated certificates replay.
/// - witness: `tests::recurrence::exp_of_one_encloses_e_and_its_certificate_replays`
/// - witness: `tests::recurrence::exp_of_log_three_holds_three`
#[inline]
pub fn series(
    argument: &NumericInterval,
    (numerator, denominator): (&Polynomial, &Polynomial),
    precision: Precision,
) -> Result<(NumericInterval, Terms), CertificateCheck>
{
    let work = Work::at(precision)?;
    let argument = ends(argument)?;
    let ratio = (numerator, denominator);
    let mut partial = Partial::start();
    radius(&work, &argument, ratio)?;
    summed(&work, &argument, ratio, &mut partial, Until::Small)?;
    loop {
        match bounded(&work, &argument, ratio, &partial) {
            Ok(pair) => return Ok((closed(pair)?, partial.terms)),
            Err(CertificateCheck::Tail) if partial.terms < Terms::MAX => {
                let next = Terms(partial.terms.0.saturating_add(1));
                summed(&work, &argument, ratio, &mut partial, Until::Count(next))?;
            },
            Err(refused) => return Err(refused),
        }
    }
}

/// The enclosure of the series of `ratio` over the argument after exactly
/// `terms` terms at `precision`: the rule of the checker.
///
/// # Specification
/// - requires: the ratio is valid, as for [`series`].
/// - ensures: the partial sum of the first `terms` terms, widened by the tail
///   bound after them. For the count that [`series`] gives, it is the interval
///   that [`series`] gives.
/// - fails: refuses a count past 65,536 as [`CertificateCheck::TermQuota`], and
///   as [`series`] otherwise, the search for a count aside.
/// - panics: none.
/// - executable: none — the clause speaks of the series' sum.
/// - intension: `terms` terms and one tail bound.
///
/// # Errors
/// - [`CertificateCheck::TermQuota`]: the count is past the term quota.
/// - As [`series`].
///
/// # Adequacy
/// - hypothesis: L3 — a step at the term quota and one past it; a step of too
///   few terms.
/// - witness: `tests::recurrence::a_step_with_no_tail_bound_is_refused_by_name`
#[inline]
pub fn series_after(
    argument: &NumericInterval,
    (numerator, denominator): (&Polynomial, &Polynomial),
    terms: Terms,
    precision: Precision,
) -> Result<NumericInterval, CertificateCheck>
{
    if terms > Terms::MAX {
        return Err(CertificateCheck::TermQuota);
    }
    let work = Work::at(precision)?;
    let argument = ends(argument)?;
    let ratio = (numerator, denominator);
    let mut partial = Partial::start();
    summed(&work, &argument, ratio, &mut partial, Until::Count(terms))?;
    return closed(bounded(&work, &argument, ratio, &partial)?);
}

/// The least natural number at which `polynomial` vanishes, or `None`.
///
/// # Specification
/// - ensures: returns the least natural `n` with `polynomial(n) = 0`. A root
///   divides the constant coefficient, and it lies within the bound of Cauchy,
///   `1 + max |c_i / c_d|`, so the search tries each divisor of the constant
///   coefficient up to that bound.
/// - panics: none.
/// - executable: none — the clause speaks of every natural number.
/// - intension: at most `2 · √|c_0|` evaluations, at most 92,682.
///
/// # Adequacy
/// - hypothesis: L3 — a root at zero, at one and past the first ten; a
///   denominator with no natural root.
/// - witness: `tests::recurrence::a_malformed_ratio_is_refused_by_name`
pub(crate) fn natural_root(polynomial: &Polynomial) -> Option<Terms>
{
    let coefficients = polynomial.coefficients();
    let constant = coefficients
        .first()
        .map_or(0_i64, |&coefficient| i64::from(i32::from(coefficient)));
    if constant == 0 {
        return Some(Terms(0));
    }
    let (&leading, lower) = coefficients.split_last()?;
    let leading = i64::from(i32::from(leading)).unsigned_abs();
    let largest = lower
        .iter()
        .map(|&coefficient| i64::from(i32::from(coefficient)).unsigned_abs())
        .max()?;
    let cauchy = largest.div_ceil(leading).saturating_add(1);
    let vanishes = |point: u64| -> Option<Terms> {
        if point > cauchy {
            return None;
        }
        let at = BigInt::from(point);
        let sum = coefficients
            .iter()
            .rev()
            .fold(BigInt::from(0_u8), |sum, &coefficient| {
                return sum.mul(&at).add(BigInt::from(i32::from(coefficient)));
            });
        if sum != BigInt::from(0_u8) {
            return None;
        }
        return u32::try_from(point).ok().map(Terms);
    };
    let size = constant.unsigned_abs();
    let mut found: Option<Terms> = None;
    let mut divisor = 1_u64;
    while divisor.saturating_mul(divisor) <= size {
        if size.checked_rem(divisor) == Some(0) {
            let cofactor = size.checked_div(divisor).unwrap_or(size);
            for point in [divisor, cofactor] {
                if let Some(root) = vanishes(point) {
                    found = Some(found.map_or(root, |known| core::cmp::min(known, root)));
                }
            }
        }
        divisor = divisor.saturating_add(1);
    }
    return found;
}
