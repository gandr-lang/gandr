//! Canonical dyadic rationals and their directed rounding.
//!
//! An exact computation must compare and combine finite numbers without
//! error. Floating point rounds each result without a record of the loss. A
//! dyadic rational is a number `m · 2^e` with an integer mantissa `m` and an
//! integer exponent `e`. A sum, a difference or a product of two dyadics is a
//! dyadic, so the arithmetic stays exact while it keeps every bit. A quotient
//! is a dyadic only when the divisor's odd part divides the dividend, so a
//! quotient usually rounds.
//!
//! [`Dyadic`] holds each value in exactly one form. A nonzero mantissa is odd,
//! and zero has the exponent zero. Two values are equal exactly when their
//! forms are equal, so equality, hashing and the exact order agree. A
//! mantissa that fits 64 bits stays inline. A wider mantissa lives on the
//! `num-bigint` carrier.
//!
//! An exact result can need many bits. Each operation therefore takes a
//! [`Precision`] and a [`Rounding`]. The result keeps at most that many
//! significant bits, rounded toward the floor or toward the ceiling, and
//! [`Rounded`] states whether bits were lost. The work of one operation is
//! bounded by the bit widths of its operands and by the precision. The gap
//! between the two exponents of a sum never sets the work: an operand far
//! below the rounding position acts only through its sign.

use core::cmp::Ordering;
use core::fmt;
use core::ops::Add as _;
use core::ops::Div as _;
use core::ops::Mul as _;
use core::ops::Neg;
use core::ops::Rem as _;
use core::ops::Shl as _;
use core::ops::Shr as _;

use anodized::spec;
use num_bigint::BigInt;

/// The power of two that scales a dyadic's mantissa.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Exponent(i32);

impl From<i32> for Exponent
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: i32) -> Self
    {
        return Self(value);
    }
}

impl From<Exponent> for i32
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: Exponent) -> Self
    {
        return value.0;
    }
}

/// A count of bits: the significant bits of a mantissa, or a shift.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BitWidth(u64);

impl From<u64> for BitWidth
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: u64) -> Self
    {
        return Self(value);
    }
}

impl From<BitWidth> for u64
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: BitWidth) -> Self
    {
        return value.0;
    }
}

impl From<Precision> for BitWidth
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: Precision) -> Self
    {
        return Self(u64::from(value.0));
    }
}

/// The most significant bits that a rounded result keeps.
///
/// A precision lies between [`Precision::MIN`] and [`Precision::MAX`]. The
/// upper bound is the quota of one operation: a sum or a product never
/// materialises more than its operands' widths and this many bits.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Precision(u32);

impl Precision
{
    /// The widest precision: 2^24 bits.
    pub const MAX: Self = Self(0x0100_0000);
    /// The narrowest precision: one bit.
    pub const MIN: Self = Self(1);
}

impl TryFrom<u32> for Precision
{
    type Error = DyadicError;

    /// A precision of `bits` significant bits.
    ///
    /// # Specification
    /// - ensures: returns the precision when `bits` lies between
    ///   [`Precision::MIN`] and [`Precision::MAX`].
    /// - fails: returns [`DyadicError::PrecisionOutOfRange`] for zero bits and
    ///   for more bits than [`Precision::MAX`].
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DyadicError::PrecisionOutOfRange`]: `bits` is zero or above the
    ///   quota.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the two boundaries each way, zero and one, the quota
    ///   and one past it, separate the range check from an off-by-one mutant.
    /// - witness: `tests::dyadic::precision_admits_exactly_its_range`
    #[inline]
    #[spec(ensures: |ref result| result.as_ref().map_or_else(
        |error| *error == DyadicError::PrecisionOutOfRange && (bits == 0 || bits > Self::MAX.0),
        |precision| precision.0 == bits,
    ))]
    fn try_from(bits: u32) -> Result<Self, DyadicError>
    {
        if !(Self::MIN.0 ..= Self::MAX.0).contains(&bits) {
            return Err(DyadicError::PrecisionOutOfRange);
        }
        return Ok(Self(bits));
    }
}

impl From<Precision> for u32
{
    /// Convert or project the represented value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: Precision) -> Self
    {
        return value.0;
    }
}

/// The direction in which a result that loses bits moves.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Rounding
{
    /// The greatest representable value at or below the exact result.
    Floor,
    /// The least representable value at or above the exact result.
    Ceiling,
}

/// Whether a rounded result equals the exact result.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Exactness
{
    /// The result is the exact value.
    Exact,
    /// The result lies strictly beside the exact value, in the rounding's
    /// direction.
    Inexact,
}

/// The sign of a number.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Sign
{
    /// Below zero.
    Negative,
    /// Zero.
    Zero,
    /// Above zero.
    Positive,
}

/// A failure of a dyadic operation.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum DyadicError
{
    /// The result's exponent lies outside the range of [`Exponent`].
    ExponentOutOfRange,
    /// A requested precision lies outside `[Precision::MIN, Precision::MAX]`.
    PrecisionOutOfRange,
    /// The divisor of a quotient is zero.
    DivisionByZero,
}

impl fmt::Display for DyadicError
{
    /// Write the failure as one line.
    ///
    /// # Specification
    /// - ensures: writes one fixed line per variant that names the failure.
    /// - fails: passes the formatter's own write failure on unchanged.
    /// - panics: none.
    /// - executable: none — a `Display` sink: the formatter is write-only.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — each variant renders one distinct line, and the
    ///   wording is not pinned.
    /// - witness: `tests::dyadic::errors_render_one_distinct_line`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::ExponentOutOfRange => f.write_str("the exponent of the result is out of range"),
            Self::PrecisionOutOfRange => f.write_str("the precision is out of range"),
            Self::DivisionByZero => f.write_str("the divisor is zero"),
        }
    }
}

impl core::error::Error for DyadicError
{
}

/// A rounded result, with the record of whether rounding lost bits.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Rounded
{
    /// The rounded value.
    value: Dyadic,
    /// Whether the rounded value equals the exact one.
    exactness: Exactness,
}

impl Rounded
{
    /// The rounded value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn value(&self) -> &Dyadic
    {
        return &self.value;
    }

    /// Whether rounding lost bits.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn exactness(&self) -> Exactness
    {
        return self.exactness;
    }

    /// The rounded value, consuming the record.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn into_value(self) -> Dyadic
    {
        return self.value;
    }
}

/// A dyadic rational `mantissa · 2^exponent` in canonical form.
///
/// A nonzero mantissa is odd. Zero has the exponent zero. A mantissa that
/// fits an `i64` is inline, and only a wider one is on the carrier. So each
/// value has exactly one form, and the derived equality and hash agree with
/// the exact order of [`Ord`].
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Dyadic
{
    /// The odd mantissa, or zero.
    mantissa: Mantissa,
    /// The power of two that scales the mantissa.
    exponent: Exponent,
}

/// A mantissa: inline when it fits an `i64`, otherwise on the carrier.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum Mantissa
{
    /// A mantissa that fits an `i64`.
    Small(i64),
    /// A mantissa outside the range of an `i64`.
    Large(BigInt),
}

/// A dyadic's mantissa as the plan codec writes it: inline or on the
/// carrier, never copied.
#[derive(Clone, Copy, Debug)]
pub(crate) enum MantissaView<'value>
{
    /// A mantissa that fits an `i64`.
    Small(i64),
    /// A mantissa outside the range of an `i64`.
    Large(&'value BigInt),
}

/// A mantissa that fits an `i64`, as the plan codec reads it back.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub(crate) struct InlineMantissa(i64);

impl From<i64> for InlineMantissa
{
    /// The mantissa `value`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: i64) -> Self
    {
        return Self(value);
    }
}

impl Dyadic
{
    /// The dyadic one.
    pub const ONE: Self = Self {
        mantissa: Mantissa::Small(1),
        exponent: Exponent(0),
    };
    /// The dyadic zero.
    pub const ZERO: Self = Self {
        mantissa: Mantissa::Small(0),
        exponent: Exponent(0),
    };

    /// The dyadic `mantissa · 2^exponent`, brought to canonical form.
    ///
    /// # Specification
    /// - ensures: the result denotes `mantissa · 2^exponent` and is canonical:
    ///   an odd mantissa, or zero with the exponent zero.
    /// - fails: returns [`DyadicError::ExponentOutOfRange`] when removing the
    ///   mantissa's trailing zeros moves the exponent past `i32::MAX`.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DyadicError::ExponentOutOfRange`]: the canonical exponent does not
    ///   fit an `i32`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the differential oracle reads every generated value
    ///   back through `mantissa` and `exponent` and compares the rational it
    ///   denotes; L3 — an even mantissa, zero with a nonzero exponent and a
    ///   mantissa beside the `i64` bounds pin the canonical form, and an
    ///   exponent at `i32::MAX` with a trailing zero pins the failure.
    /// - witness: `tests::dyadic::new_strips_trailing_zeros_into_the_exponent`
    /// - witness: `tests::dyadic::new_keeps_the_i64_boundary_canonical`
    /// - witness: `tests::dyadic::new_refuses_an_exponent_past_its_range`
    /// - witness: `tests::oracle::canonical_form_denotes_its_parts`
    #[inline]
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |value| value.form() == Form::Canonical))]
    pub fn new(
        mantissa: BigInt,
        exponent: Exponent,
    ) -> Result<Self, DyadicError>
    {
        let raw = Unrounded {
            mantissa: Wide::Large(mantissa),
            exponent: Scale::of(exponent),
        };
        return raw.canonical();
    }

    /// The mantissa, odd unless the value is zero.
    ///
    /// # Specification
    /// - ensures: `mantissa · 2^exponent` is the value.
    /// - provides: an owned integer; an inline mantissa allocates it.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the oracle rebuilds each value from its parts.
    /// - witness: `tests::oracle::canonical_form_denotes_its_parts`
    #[inline]
    #[must_use]
    #[spec(ensures: |ref result| (result.sign() == num_bigint::Sign::NoSign) == (self.sign() == Sign::Zero))]
    pub fn mantissa(&self) -> BigInt
    {
        match self.mantissa {
            Mantissa::Small(value) => BigInt::from(value),
            Mantissa::Large(ref value) => value.clone(),
        }
    }

    /// The exponent.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn exponent(&self) -> Exponent
    {
        return self.exponent;
    }

    /// The significant bits of the mantissa's magnitude; zero has none.
    ///
    /// # Specification
    /// - ensures: returns the bit length of the mantissa's magnitude, and zero
    ///   for the value zero.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, one, a 63-bit and a 64-bit mantissa separate
    ///   the inline and the carried widths.
    /// - witness: `tests::dyadic::width_counts_the_magnitude_bits`
    #[inline]
    #[must_use]
    #[spec(ensures: |ref result| (result.0 == 0) == (self.sign() == Sign::Zero))]
    pub fn width(&self) -> BitWidth
    {
        return self.term().width();
    }

    /// The sign.
    ///
    /// # Specification
    /// - ensures: returns the sign of the value.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero and an inline and a carried value of each sign.
    /// - witness: `tests::dyadic::sign_reads_both_carriers`
    #[inline]
    #[must_use]
    #[spec(ensures: |ref result| (*result == Sign::Zero) == (*self == Self::ZERO))]
    pub fn sign(&self) -> Sign
    {
        return self.term().sign();
    }

    /// The value rounded to `precision` significant bits toward `rounding`.
    ///
    /// # Specification
    /// - ensures: the result is canonical, keeps at most `precision` bits, and
    ///   is the floor or the ceiling of the value on that grid. It is exact
    ///   when the value already fits.
    /// - fails: returns [`DyadicError::ExponentOutOfRange`] when the rounded
    ///   exponent passes `i32::MAX`.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DyadicError::ExponentOutOfRange`]: the rounded exponent does not fit
    ///   an `i32`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the rational oracle computes the floor and the
    ///   ceiling on the grid of each precision and compares them exactly; a
    ///   swapped direction or an off-by-one shift disagrees with it.
    /// - witness: `tests::oracle::round_is_the_directed_neighbour_on_the_grid`
    /// - witness: `tests::dyadic::round_refuses_an_exponent_past_its_range`
    #[inline]
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |rounded| rounded.value.form() == Form::Canonical && rounded.value.width() <= BitWidth::from(precision)))]
    pub fn round(
        &self,
        precision: Precision,
        rounding: Rounding,
    ) -> Result<Rounded, DyadicError>
    {
        return self.term().owned().round(precision, rounding);
    }

    /// The sum `self + other`, rounded to `precision` bits toward `rounding`.
    ///
    /// # Specification
    /// - ensures: the result is the floor or the ceiling of the exact sum on
    ///   the grid of `precision` significant bits, and is canonical.
    /// - fails: returns [`DyadicError::ExponentOutOfRange`] when the result's
    ///   exponent leaves the range of `i32`.
    /// - panics: none.
    /// - intension: the work is bounded by the two operand widths and the
    ///   precision. An operand whose magnitude lies below half the unit in the
    ///   last place of the other is replaced by a value of its sign at that
    ///   position, so the exponent gap never sets the work.
    ///
    /// # Errors
    /// - [`DyadicError::ExponentOutOfRange`]: the exponent of the result does
    ///   not fit an `i32`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the rational oracle forms the exact sum and rounds it
    ///   on the grid; operands with exponent gaps on both sides of the sticky
    ///   threshold, of each sign and of both carriers, separate a wrong sticky
    ///   position, a lost sign and a swapped direction.
    /// - witness: `tests::oracle::sum_and_difference_are_the_directed_neighbours`
    /// - witness: `tests::oracle::far_operands_round_by_their_sign`
    /// - witness: `tests::dyadic::far_sum_costs_no_wide_shift`
    #[inline]
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |rounded| rounded.value.form() == Form::Canonical && rounded.value.width() <= BitWidth::from(precision)))]
    pub fn add(
        &self,
        other: &Self,
        precision: Precision,
        rounding: Rounding,
    ) -> Result<Rounded, DyadicError>
    {
        return rounded_sum(self.term(), other.term(), precision, rounding);
    }

    /// The difference `self - other`, rounded to `precision` bits toward
    /// `rounding`.
    ///
    /// # Specification
    /// - ensures: the result is the floor or the ceiling of the exact
    ///   difference on the grid of `precision` significant bits, and is
    ///   canonical.
    /// - fails: returns [`DyadicError::ExponentOutOfRange`] when the result's
    ///   exponent leaves the range of `i32`.
    /// - panics: none.
    /// - intension: the bound of [`Dyadic::add`]; the negation of `other`
    ///   allocates nothing.
    ///
    /// # Errors
    /// - [`DyadicError::ExponentOutOfRange`]: the exponent of the result does
    ///   not fit an `i32`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the rational oracle forms the exact difference; a
    ///   mutant that adds instead of subtracting, or flips the wrong operand,
    ///   disagrees with it.
    /// - witness: `tests::oracle::sum_and_difference_are_the_directed_neighbours`
    /// - witness: `tests::oracle::far_operands_round_by_their_sign`
    #[inline]
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |rounded| rounded.value.form() == Form::Canonical && rounded.value.width() <= BitWidth::from(precision)))]
    pub fn sub(
        &self,
        other: &Self,
        precision: Precision,
        rounding: Rounding,
    ) -> Result<Rounded, DyadicError>
    {
        let mut subtrahend = other.term();
        subtrahend.polarity = Polarity::Flip;
        return rounded_sum(self.term(), subtrahend, precision, rounding);
    }

    /// The product `self · other`, rounded to `precision` bits toward
    /// `rounding`.
    ///
    /// # Specification
    /// - ensures: the result is the floor or the ceiling of the exact product
    ///   on the grid of `precision` significant bits, and is canonical.
    /// - fails: returns [`DyadicError::ExponentOutOfRange`] when the result's
    ///   exponent leaves the range of `i32`.
    /// - panics: none.
    /// - intension: the exact product is formed first, so the work is that of
    ///   one multiplication of the two mantissas.
    ///
    /// # Errors
    /// - [`DyadicError::ExponentOutOfRange`]: the exponent of the result does
    ///   not fit an `i32`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the rational oracle forms the exact product and
    ///   rounds it; L3 — exponents whose sum leaves the `i32` range pin the
    ///   failure.
    /// - witness: `tests::oracle::product_is_the_directed_neighbour`
    /// - witness: `tests::dyadic::product_refuses_an_exponent_past_its_range`
    #[inline]
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |rounded| rounded.value.form() == Form::Canonical && rounded.value.width() <= BitWidth::from(precision)))]
    pub fn mul(
        &self,
        other: &Self,
        precision: Precision,
        rounding: Rounding,
    ) -> Result<Rounded, DyadicError>
    {
        return self.exact_product(other)?.round(precision, rounding);
    }

    /// The exact product, before canonical form and rounding.
    ///
    /// # Specification
    /// - ensures: the result denotes `self · other` exactly.
    /// - fails: returns [`DyadicError::ExponentOutOfRange`] when the sum of the
    ///   exponents overflows the intermediate exponent.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DyadicError::ExponentOutOfRange`]: the exponent sum overflows.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — through [`Dyadic::mul`] and the interval product,
    ///   both held to the rational oracle.
    /// - witness: `tests::oracle::product_is_the_directed_neighbour`
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |exact| (exact.sign() == Sign::Zero) == (self.sign() == Sign::Zero || other.sign() == Sign::Zero)))]
    #[inline]
    pub(crate) fn exact_product(
        &self,
        other: &Self,
    ) -> Result<Unrounded, DyadicError>
    {
        return product(self.term(), other.term());
    }

    /// The quotient `self / other`, rounded to `precision` bits toward
    /// `rounding`.
    ///
    /// # Specification
    /// - ensures: the result is the floor or the ceiling of the exact quotient
    ///   on the grid of `precision` significant bits, and is canonical.
    /// - fails: returns [`DyadicError::DivisionByZero`] when `other` is zero,
    ///   and [`DyadicError::ExponentOutOfRange`] when the result's exponent
    ///   leaves the range of `i32`.
    /// - panics: none.
    /// - intension: one integer division. The dividend gains low zero bits
    ///   until it is `precision + 2` bits wider than the divisor. The division
    ///   stays inline in an `i128` when the widened dividend fits. A nonzero
    ///   remainder sets one sticky bit, so the rounding sees on which side of
    ///   the grid the exact quotient lies.
    ///
    /// # Errors
    /// - [`DyadicError::DivisionByZero`]: the divisor is zero.
    /// - [`DyadicError::ExponentOutOfRange`]: the exponent of the result does
    ///   not fit an `i32`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the rational oracle forms the exact quotient and
    ///   rounds it. Generated operands give quotients with and without a
    ///   remainder, of both signs, inline and on the carrier. A mutant that
    ///   drops the sticky bit or turns its sign disagrees with the oracle.
    /// - witness: `tests::oracle::quotient_is_the_directed_neighbour`
    /// - witness: `tests::dyadic::quotient_refuses_a_zero_divisor`
    #[inline]
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |rounded| rounded.value.form() == Form::Canonical && rounded.value.width() <= BitWidth::from(precision)))]
    pub fn div(
        &self,
        other: &Self,
        precision: Precision,
        rounding: Rounding,
    ) -> Result<Rounded, DyadicError>
    {
        return quotient(self.term(), other.term(), precision)?.round(precision, rounding);
    }

    /// Whether the value is in canonical form.
    ///
    /// # Specification
    /// - ensures: answers [`Form::Canonical`] exactly when the mantissa is odd,
    ///   or zero with the exponent zero, and a carried mantissa lies outside
    ///   the `i64` range.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every constructor's witness reads it, and the
    ///   canonical zero is the one zero.
    /// - witness: `tests::dyadic::new_keeps_the_i64_boundary_canonical`
    #[spec(ensures: |ref result| *result == Form::Other || self.sign() != Sign::Zero || *self == Self::ZERO)]
    fn form(&self) -> Form
    {
        let canonical = match self.mantissa {
            Mantissa::Small(0) => self.exponent.0 == 0_i32,
            Mantissa::Small(value) => value.trailing_zeros() == 0,
            Mantissa::Large(ref value) => {
                i64::try_from(value).is_err() && value.trailing_zeros() == Some(0)
            },
        };
        return if canonical {
            Form::Canonical
        }
        else {
            Form::Other
        };
    }

    /// A borrowed view for the arithmetic.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn term(&self) -> Term<'_>
    {
        let digits = match self.mantissa {
            Mantissa::Small(value) => Digits::Small(i128::from(value)),
            Mantissa::Large(ref value) => Digits::Large(value),
        };
        return Term {
            digits,
            exponent: Scale::of(self.exponent),
            polarity: Polarity::Keep,
        };
    }

    /// The mantissa, borrowed in the form the value holds it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn mantissa_view(&self) -> MantissaView<'_>
    {
        return match self.mantissa {
            Mantissa::Small(value) => MantissaView::Small(value),
            Mantissa::Large(ref value) => MantissaView::Large(value),
        };
    }

    /// The dyadic `mantissa · 2^exponent` from an inline mantissa, brought
    /// to canonical form with no carrier allocation.
    ///
    /// # Specification
    /// - ensures: as [`Dyadic::new`] of the same parts.
    /// - fails: returns [`DyadicError::ExponentOutOfRange`] when removing the
    ///   mantissa's trailing zeros moves the exponent past `i32::MAX`.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DyadicError::ExponentOutOfRange`]: the canonical exponent does not
    ///   fit an `i32`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the plan round trip reads every generated inline
    ///   constant back through it, and the codec refuses a padded mantissa.
    /// - witness: `tests::plan::encoding_round_trips_generated_plans`
    #[inline]
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |value| value.form() == Form::Canonical))]
    pub(crate) fn from_inline(
        mantissa: InlineMantissa,
        exponent: Exponent,
    ) -> Result<Self, DyadicError>
    {
        let raw = Unrounded {
            mantissa: Wide::Small(i128::from(mantissa.0)),
            exponent: Scale::of(exponent),
        };
        return raw.canonical();
    }
}

impl From<i64> for Dyadic
{
    /// The integer `value` as a dyadic.
    ///
    /// # Specification
    /// - ensures: the result denotes `value` and is canonical.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, an odd value, a power of two and `i64::MIN`
    ///   separate the trailing-zero count.
    /// - witness: `tests::dyadic::integers_enter_in_canonical_form`
    #[inline]
    #[spec(ensures: |ref result| result.form() == Form::Canonical)]
    fn from(value: i64) -> Self
    {
        if value == 0 {
            return Self::ZERO;
        }
        let zeros = value.trailing_zeros();
        let mantissa = value.checked_shr(zeros).map_or_else(
            || Mantissa::Large(BigInt::from(value).shr(zeros)),
            Mantissa::Small,
        );
        return Self {
            mantissa,
            exponent: Exponent(zeros.cast_signed()),
        };
    }
}

impl Ord for Dyadic
{
    /// The exact order of the two values.
    ///
    /// # Specification
    /// - ensures: orders the denoted rationals; `Equal` exactly when the
    ///   canonical forms are equal.
    /// - panics: none.
    /// - intension: two inline values whose exponents lie within 62 bits of
    ///   each other compare with no allocation.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the rational oracle compares by cross multiplication;
    ///   generated pairs share a top bit often, so the aligned comparison is
    ///   reached. L3 — values of each sign and both carriers at one top bit.
    /// - witness: `tests::oracle::order_is_the_rational_order`
    /// - witness: `tests::dyadic::order_crosses_the_carriers`
    #[inline]
    #[spec(ensures: |ref result| (*result == Ordering::Equal) == (self == other))]
    fn cmp(
        &self,
        other: &Self,
    ) -> Ordering
    {
        return compare(self.term(), other.term());
    }
}

impl PartialOrd for Dyadic
{
    /// The exact order, which is total.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn partial_cmp(
        &self,
        other: &Self,
    ) -> Option<Ordering>
    {
        return Some(self.cmp(other));
    }
}

impl Neg for &Dyadic
{
    type Output = Dyadic;

    /// The negated value.
    ///
    /// # Specification
    /// - ensures: the result denotes `-self` and is canonical.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero, an inline value and a carried value whose
    ///   magnitude lies just past the `i64` range.
    /// - witness: `tests::dyadic::negation_keeps_the_carrier_class`
    #[inline]
    #[spec(ensures: |ref result| result.form() == Form::Canonical && result.sign() == match self.sign() { Sign::Negative => Sign::Positive, Sign::Zero => Sign::Zero, Sign::Positive => Sign::Negative })]
    fn neg(self) -> Dyadic
    {
        let mantissa = match self.mantissa {
            Mantissa::Small(value) => value.checked_neg().map_or_else(
                || Wide::Large(BigInt::from(value).neg()).into_mantissa(),
                Mantissa::Small,
            ),
            Mantissa::Large(ref value) => Wide::Large(value.neg()).into_mantissa(),
        };
        return Dyadic {
            mantissa,
            exponent: self.exponent,
        };
    }
}

/// An exponent of an intermediate result, wide enough that a sum of two
/// exponents and a bit count is checked rather than wrapped.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Scale(i64);

impl Scale
{
    /// The intermediate form of an exponent.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn of(exponent: Exponent) -> Self
    {
        return Self(i64::from(exponent.0));
    }

    /// This scale raised by `bits`.
    ///
    /// # Specification
    /// - ensures: returns `self + bits`.
    /// - fails: returns [`DyadicError::ExponentOutOfRange`] when the sum
    ///   overflows an `i64`.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DyadicError::ExponentOutOfRange`]: the sum overflows.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every rounding raises the exponent by the bits it
    ///   drops, and the oracle compares the result.
    /// - witness: `tests::oracle::round_is_the_directed_neighbour_on_the_grid`
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |raised| i128::from(self.0).checked_add(i128::from(bits.0)) == Some(i128::from(raised.0))))]
    #[inline]
    fn raised(
        self,
        bits: BitWidth,
    ) -> Result<Self, DyadicError>
    {
        let bits = i64::try_from(bits.0).map_err(|_overflow| DyadicError::ExponentOutOfRange)?;
        return self
            .0
            .checked_add(bits)
            .map(Self)
            .ok_or(DyadicError::ExponentOutOfRange);
    }

    /// This scale lowered by `bits`.
    ///
    /// # Specification
    /// - ensures: returns `self - bits`.
    /// - fails: returns [`DyadicError::ExponentOutOfRange`] when the difference
    ///   overflows an `i64`.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DyadicError::ExponentOutOfRange`]: the difference overflows.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the sticky position of a sum is lowered from the
    ///   larger operand's top bit, and the oracle checks the sum.
    /// - witness: `tests::oracle::far_operands_round_by_their_sign`
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |lowered| i128::from(self.0).checked_sub(i128::from(bits.0)) == Some(i128::from(lowered.0))))]
    #[inline]
    fn lowered(
        self,
        bits: BitWidth,
    ) -> Result<Self, DyadicError>
    {
        let bits = i64::try_from(bits.0).map_err(|_overflow| DyadicError::ExponentOutOfRange)?;
        return self
            .0
            .checked_sub(bits)
            .map(Self)
            .ok_or(DyadicError::ExponentOutOfRange);
    }

    /// The sum of two scales.
    ///
    /// # Specification
    /// - ensures: returns `self + other`.
    /// - fails: returns [`DyadicError::ExponentOutOfRange`] when the sum
    ///   overflows an `i64`.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DyadicError::ExponentOutOfRange`]: the sum overflows.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — a product's exponent is this sum, and the oracle
    ///   checks the product.
    /// - witness: `tests::oracle::product_is_the_directed_neighbour`
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |sum| i128::from(self.0).checked_add(i128::from(other.0)) == Some(i128::from(sum.0))))]
    #[inline]
    fn plus(
        self,
        other: Self,
    ) -> Result<Self, DyadicError>
    {
        return self
            .0
            .checked_add(other.0)
            .map(Self)
            .ok_or(DyadicError::ExponentOutOfRange);
    }

    /// The nonnegative gap `self - lower`, as a bit count.
    ///
    /// # Specification
    /// - requires: `lower <= self`.
    /// - ensures: returns `self - lower`.
    /// - fails: returns [`DyadicError::ExponentOutOfRange`] when the difference
    ///   overflows.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DyadicError::ExponentOutOfRange`]: the difference overflows.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every alignment shift is this gap, and the oracle
    ///   checks each sum and comparison.
    /// - witness: `tests::oracle::order_is_the_rational_order`
    #[spec(requires: lower <= self, ensures: |ref result| result.as_ref().map_or(true, |gap| i128::from(self.0).checked_sub(i128::from(lower.0)) == Some(i128::from(gap.0))))]
    #[inline]
    fn gap(
        self,
        lower: Self,
    ) -> Result<BitWidth, DyadicError>
    {
        let gap = self
            .0
            .checked_sub(lower.0)
            .ok_or(DyadicError::ExponentOutOfRange)?;
        return u64::try_from(gap)
            .map(BitWidth)
            .map_err(|_negative| DyadicError::ExponentOutOfRange);
    }

    /// This scale as an exponent.
    ///
    /// # Specification
    /// - ensures: returns the same value as an [`Exponent`].
    /// - fails: returns [`DyadicError::ExponentOutOfRange`] outside the `i32`
    ///   range.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DyadicError::ExponentOutOfRange`]: the value does not fit an `i32`.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a product of two exponents near `i32::MAX`.
    /// - witness: `tests::dyadic::product_refuses_an_exponent_past_its_range`
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |exponent| i64::from(exponent.0) == self.0))]
    #[inline]
    fn narrowed(self) -> Result<Exponent, DyadicError>
    {
        return i32::try_from(self.0)
            .map(Exponent)
            .map_err(|_overflow| DyadicError::ExponentOutOfRange);
    }
}

/// Whether a dyadic's fields hold its canonical form.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Form
{
    /// An odd mantissa, or zero with the exponent zero, inline whenever it
    /// fits an `i64`.
    Canonical,
    /// Any other form.
    Other,
}

/// The sign that a term carries beside its digits.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Polarity
{
    /// The term denotes its digits.
    Keep,
    /// The term denotes the negation of its digits.
    Flip,
}

/// Borrowed digits of a mantissa: inline, or on the carrier.
#[derive(Clone, Copy, Debug)]
enum Digits<'value>
{
    /// Inline digits.
    Small(i128),
    /// Digits on the carrier.
    Large(&'value BigInt),
}

/// A borrowed operand: `polarity · digits · 2^exponent`.
#[derive(Clone, Copy, Debug)]
struct Term<'value>
{
    /// The digits.
    digits: Digits<'value>,
    /// The power of two that scales the digits.
    exponent: Scale,
    /// Whether the term denotes the negation of its digits.
    polarity: Polarity,
}

impl Term<'_>
{
    /// The sign of the denoted value.
    ///
    /// # Specification
    /// - ensures: returns the sign of `polarity · digits`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the sign decides the comparison and the sticky
    ///   operand, both held to the oracle.
    /// - witness: `tests::oracle::far_operands_round_by_their_sign`
    #[spec(ensures: |ref result| (*result == Sign::Zero) == (self.width().0 == 0))]
    #[inline]
    fn sign(self) -> Sign
    {
        let digits = match self.digits {
            Digits::Small(value) => match value.cmp(&0) {
                Ordering::Less => Sign::Negative,
                Ordering::Equal => Sign::Zero,
                Ordering::Greater => Sign::Positive,
            },
            Digits::Large(value) => match value.sign() {
                num_bigint::Sign::Minus => Sign::Negative,
                num_bigint::Sign::NoSign => Sign::Zero,
                num_bigint::Sign::Plus => Sign::Positive,
            },
        };
        return match (self.polarity, digits) {
            (Polarity::Keep, sign) | (Polarity::Flip, sign @ Sign::Zero) => sign,
            (Polarity::Flip, Sign::Negative) => Sign::Positive,
            (Polarity::Flip, Sign::Positive) => Sign::Negative,
        };
    }

    /// The bit length of the digits' magnitude.
    ///
    /// # Specification
    /// - ensures: returns the bit length of `|digits|`, zero for zero.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — through [`Dyadic::width`].
    /// - witness: `tests::dyadic::width_counts_the_magnitude_bits`
    #[spec(ensures: |ref result| result.0 <= 128 || matches!(self.digits, Digits::Large(_)))]
    #[inline]
    fn width(self) -> BitWidth
    {
        return match self.digits {
            Digits::Small(value) => BitWidth(u64::from(
                i128::BITS.saturating_sub(value.unsigned_abs().leading_zeros()),
            )),
            Digits::Large(value) => BitWidth(value.bits()),
        };
    }

    /// The exclusive bound of the magnitude: `|value| < 2^top`.
    ///
    /// # Specification
    /// - requires: the term is nonzero.
    /// - ensures: returns `exponent + width`, so `2^(top - 1) <= |value| <
    ///   2^top`.
    /// - fails: returns [`DyadicError::ExponentOutOfRange`] when the sum
    ///   overflows an `i64`.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DyadicError::ExponentOutOfRange`]: the sum overflows.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the top bit decides most comparisons and the sticky
    ///   threshold, both held to the oracle.
    /// - witness: `tests::oracle::order_is_the_rational_order`
    #[spec(requires: self.sign() != Sign::Zero)]
    #[inline]
    fn top(self) -> Result<Scale, DyadicError>
    {
        return self.exponent.raised(self.width());
    }

    /// The signed digits on the carrier, the polarity applied.
    ///
    /// # Specification
    /// - ensures: returns `polarity · digits` as an integer on the carrier.
    /// - panics: none.
    /// - intension: allocates the integer.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every sum wider than 128 bits reads it, and the
    ///   oracle checks the sum.
    /// - witness: `tests::oracle::sum_and_difference_are_the_directed_neighbours`
    #[spec(ensures: |ref result| (result.sign() == num_bigint::Sign::NoSign) == (self.sign() == Sign::Zero))]
    fn signed_big(self) -> BigInt
    {
        let digits = match self.digits {
            Digits::Small(value) => BigInt::from(value),
            Digits::Large(value) => value.clone(),
        };
        return match self.polarity {
            Polarity::Keep => digits,
            Polarity::Flip => digits.neg(),
        };
    }

    /// The signed digits as an intermediate integer, the polarity applied.
    ///
    /// # Specification
    /// - ensures: returns `polarity · digits`.
    /// - panics: none.
    /// - intension: allocates only for digits on the carrier.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — through [`Dyadic::round`], held to the oracle.
    /// - witness: `tests::oracle::round_is_the_directed_neighbour_on_the_grid`
    #[spec(ensures: |ref result| result.sign() == self.sign())]
    #[inline]
    fn signed_wide(self) -> Wide
    {
        return match (self.digits, self.polarity) {
            (Digits::Small(value), Polarity::Keep) => Wide::Small(value),
            (Digits::Small(value), Polarity::Flip) => value
                .checked_neg()
                .map_or_else(|| Wide::Large(BigInt::from(value).neg()), Wide::Small),
            (Digits::Large(_), Polarity::Keep | Polarity::Flip) => Wide::Large(self.signed_big()),
        };
    }

    /// The term as an owned intermediate value.
    ///
    /// # Specification
    /// - ensures: returns an intermediate value denoting the same number.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — through [`Dyadic::round`], held to the oracle.
    /// - witness: `tests::oracle::round_is_the_directed_neighbour_on_the_grid`
    #[spec(ensures: |ref result| result.sign() == self.sign() && result.exponent == self.exponent)]
    #[inline]
    fn owned(self) -> Unrounded
    {
        return Unrounded {
            mantissa: self.signed_wide(),
            exponent: self.exponent,
        };
    }

    /// The magnitude of the digits, the polarity ignored.
    ///
    /// # Specification
    /// - ensures: returns `|digits|`.
    /// - panics: none.
    /// - intension: inline digits stay inline; digits on the carrier are
    ///   copied.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every comparison of two values with one top bit reads
    ///   it, held to the oracle.
    /// - witness: `tests::oracle::order_is_the_rational_order`
    #[spec(ensures: |ref result| result.sign() != Sign::Negative && result.width() == self.width())]
    #[inline]
    fn magnitude(self) -> Wide
    {
        return match self.digits {
            Digits::Small(value) => value.checked_abs().map_or_else(
                || Wide::Large(BigInt::from(value.unsigned_abs())),
                Wide::Small,
            ),
            Digits::Large(value) => Wide::Large(BigInt::from(value.magnitude().clone())),
        };
    }
}

/// The two terms as integers on the grid of the lower exponent.
///
/// # Specification
/// - ensures: returns `(a', b', low)` with `a = a' · 2^low` and `b = b' ·
///   2^low`, where `low` is the lower of the two exponents.
/// - fails: returns [`DyadicError::ExponentOutOfRange`] when a gap overflows.
/// - panics: none.
/// - intension: an inline value stays inline while its shift fits an `i128`, so
///   two narrow terms align with no allocation.
///
/// # Errors
/// - [`DyadicError::ExponentOutOfRange`]: an alignment gap overflows.
///
/// # Adequacy
/// - hypothesis: L2 — sums through both carriers are held to the oracle;
///   generated widths and gaps straddle the inline bound.
/// - witness: `tests::oracle::sum_and_difference_are_the_directed_neighbours`
#[spec(ensures: |ref result| result.as_ref().map_or(true, |&(ref left, ref right, low)| left.sign() == lhs.sign() && right.sign() == rhs.sign() && low == lhs.exponent.min(rhs.exponent)))]
#[inline]
fn aligned(
    lhs: Term<'_>,
    rhs: Term<'_>,
) -> Result<(Wide, Wide, Scale), DyadicError>
{
    let low = lhs.exponent.min(rhs.exponent);
    let lhs_shift = lhs.exponent.gap(low)?;
    let rhs_shift = rhs.exponent.gap(low)?;
    let left = lhs.signed_wide().shifted_up(lhs_shift);
    let right = rhs.signed_wide().shifted_up(rhs_shift);
    return Ok((left, right, low));
}

/// The exact sum of two terms.
///
/// # Specification
/// - ensures: returns an intermediate value denoting `lhs + rhs`.
/// - fails: returns [`DyadicError::ExponentOutOfRange`] when an alignment gap
///   overflows.
/// - panics: none.
///
/// # Errors
/// - [`DyadicError::ExponentOutOfRange`]: an alignment gap overflows.
///
/// # Adequacy
/// - hypothesis: L2 — every rounded sum and difference reads it, held to the
///   oracle.
/// - witness: `tests::oracle::sum_and_difference_are_the_directed_neighbours`
#[spec(ensures: |ref result| result.as_ref().map_or(true, |sum| sum.exponent == lhs.exponent.min(rhs.exponent)))]
#[inline]
fn exact_sum(
    lhs: Term<'_>,
    rhs: Term<'_>,
) -> Result<Unrounded, DyadicError>
{
    let (left, right, low) = aligned(lhs, rhs)?;
    return Ok(Unrounded {
        mantissa: left.plus(right),
        exponent: low,
    });
}

/// The sum of two terms rounded to `precision` bits toward `rounding`.
///
/// # Specification
/// - ensures: returns the floor or the ceiling of `lhs + rhs` on the grid of
///   `precision` significant bits.
/// - fails: returns [`DyadicError::ExponentOutOfRange`] when the result's
///   exponent leaves the range of `i32`.
/// - panics: none.
/// - intension: let `big` be the term with the higher top bit, and let `g` be
///   the lower of its exponent and `top(big) - 1 - precision`. When the other
///   term lies below `2^(g - 1)`, it is replaced by its sign times `2^(g - 2)`.
///   Both sums then lie in one open cell of the result's grid, so the rounded
///   result is the same, and the aligned width stays below the two widths plus
///   the precision plus three bits.
///
/// # Errors
/// - [`DyadicError::ExponentOutOfRange`]: the result's exponent does not fit an
///   `i32`.
///
/// # Adequacy
/// - hypothesis: L2 — operands on both sides of the sticky threshold, held to
///   the oracle; L3 — a sum whose exponent gap is near `2^32` finishes with no
///   wide shift.
/// - witness: `tests::oracle::far_operands_round_by_their_sign`
/// - witness: `tests::dyadic::far_sum_costs_no_wide_shift`
#[spec(ensures: |ref result| result.as_ref().map_or(true, |rounded| rounded.value.form() == Form::Canonical && rounded.value.width() <= BitWidth::from(precision)))]
#[inline]
fn rounded_sum(
    lhs: Term<'_>,
    rhs: Term<'_>,
    precision: Precision,
    rounding: Rounding,
) -> Result<Rounded, DyadicError>
{
    // Two inline operands within 61 bits of each other align inside an
    // `i128`, so their exact sum is cheaper than the sticky bound.
    if let (Digits::Small(_), Digits::Small(_)) = (lhs.digits, rhs.digits)
        && lhs.width().0 <= 64
        && rhs.width().0 <= 64
        && lhs.exponent.0.abs_diff(rhs.exponent.0) <= 61
    {
        return exact_sum(lhs, rhs)?.round(precision, rounding);
    }
    if lhs.sign() == Sign::Zero {
        return rhs.owned().round(precision, rounding);
    }
    if rhs.sign() == Sign::Zero {
        return lhs.owned().round(precision, rounding);
    }
    let lhs_top = lhs.top()?;
    let rhs_top = rhs.top()?;
    let (big, big_top, small, small_top) = if lhs_top >= rhs_top {
        (lhs, lhs_top, rhs, rhs_top)
    }
    else {
        (rhs, rhs_top, lhs, lhs_top)
    };
    let guard = big_top
        .lowered(BitWidth(1))?
        .lowered(BitWidth::from(precision))?
        .min(big.exponent);
    if small_top < guard {
        let sticky = match small.sign() {
            Sign::Negative => Digits::Small(-1),
            Sign::Zero => Digits::Small(0),
            Sign::Positive => Digits::Small(1),
        };
        let sticky = Term {
            digits: sticky,
            exponent: guard.lowered(BitWidth(2))?,
            polarity: Polarity::Keep,
        };
        return exact_sum(big, sticky)?.round(precision, rounding);
    }
    return exact_sum(lhs, rhs)?.round(precision, rounding);
}

/// The exact product of two terms.
///
/// # Specification
/// - ensures: returns an intermediate value denoting `lhs · rhs`.
/// - fails: returns [`DyadicError::ExponentOutOfRange`] when the sum of the
///   exponents overflows.
/// - panics: none.
/// - intension: two inline terms whose product fits an `i128` multiply inline
///   with no allocation.
///
/// # Errors
/// - [`DyadicError::ExponentOutOfRange`]: the exponent sum overflows.
///
/// # Adequacy
/// - hypothesis: L2 — every rounded product reads it, held to the oracle;
///   generated widths straddle the inline bound.
/// - witness: `tests::oracle::product_is_the_directed_neighbour`
#[spec(ensures: |ref result| result.as_ref().map_or(true, |exact| (exact.sign() == Sign::Zero) == (lhs.sign() == Sign::Zero || rhs.sign() == Sign::Zero)))]
#[inline]
fn product(
    lhs: Term<'_>,
    rhs: Term<'_>,
) -> Result<Unrounded, DyadicError>
{
    let exponent = lhs.exponent.plus(rhs.exponent)?;
    let mantissa = match (lhs.signed_wide(), rhs.signed_wide()) {
        (Wide::Small(left), Wide::Small(right)) => left.checked_mul(right).map_or_else(
            || Wide::Large(BigInt::from(left).mul(BigInt::from(right))),
            Wide::Small,
        ),
        (Wide::Small(left), Wide::Large(right)) => Wide::Large(right.mul(left)),
        (Wide::Large(left), Wide::Small(right)) => Wide::Large(left.mul(right)),
        (Wide::Large(left), Wide::Large(right)) => Wide::Large(left.mul(right)),
    };
    return Ok(Unrounded { mantissa, exponent });
}

/// The quotient of two terms before rounding: exact, or with one sticky bit
/// below its top `precision + 2` bits.
///
/// # Specification
/// - ensures: when the division leaves no remainder, the result denotes `lhs /
///   rhs` exactly. Otherwise its mantissa is wider than `precision + 2` bits,
///   and it lies strictly between the same two neighbours on the grid of
///   `precision` significant bits as `lhs / rhs`. Both then round to the same
///   value, and the rounding is inexact.
/// - fails: returns [`DyadicError::DivisionByZero`] when `rhs` is zero, and
///   [`DyadicError::ExponentOutOfRange`] when the exponent arithmetic
///   overflows.
/// - panics: none.
/// - intension: inline in an `i128` when the widened dividend fits 125 bits,
///   otherwise one division on the carrier.
///
/// # Errors
/// - [`DyadicError::DivisionByZero`]: the divisor is zero.
/// - [`DyadicError::ExponentOutOfRange`]: the exponent arithmetic overflows.
///
/// # Adequacy
/// - hypothesis: L2 — through [`Dyadic::div`], held to the oracle.
/// - witness: `tests::oracle::quotient_is_the_directed_neighbour`
#[spec(ensures: |ref result| result.as_ref().map_or(true, |exact| (exact.sign() == Sign::Zero) == (lhs.sign() == Sign::Zero)))]
#[inline]
fn quotient(
    lhs: Term<'_>,
    rhs: Term<'_>,
    precision: Precision,
) -> Result<Unrounded, DyadicError>
{
    if rhs.sign() == Sign::Zero {
        return Err(DyadicError::DivisionByZero);
    }
    if lhs.sign() == Sign::Zero {
        return Ok(Unrounded::zero());
    }
    // The widened dividend is at least `precision + 2` bits wider than the
    // divisor, so the integer quotient keeps at least `precision + 2` bits.
    let shift = BitWidth(
        u64::from(precision.0)
            .checked_add(2)
            .and_then(|bits| bits.checked_add(rhs.width().0))
            .ok_or(DyadicError::ExponentOutOfRange)?
            .saturating_sub(lhs.width().0),
    );
    let inline = match (lhs.digits, rhs.digits) {
        (Digits::Small(_), Digits::Small(_)) => (|| {
            let (Wide::Small(dividend), Wide::Small(divisor)) =
                (lhs.signed_wide(), rhs.signed_wide())
            else {
                return None;
            };
            if lhs.width().0.checked_add(shift.0)? > 125 {
                return None;
            }
            let dividend = dividend.checked_shl(u32::try_from(shift.0).ok()?)?;
            let quotient = dividend.checked_div(divisor)?;
            if dividend.checked_rem(divisor)? == 0 {
                return Some((Wide::Small(quotient), Exactness::Exact));
            }
            let sticky: i128 = if lhs.sign() == rhs.sign() { 1 } else { -1 };
            let mantissa = quotient.checked_mul(2)?.checked_add(sticky)?;
            return Some((Wide::Small(mantissa), Exactness::Inexact));
        })(),
        (Digits::Small(_) | Digits::Large(_), Digits::Large(_))
        | (Digits::Large(_), Digits::Small(_)) => None,
    };
    let (mantissa, exactness) = inline.unwrap_or_else(|| carried_quotient(lhs, rhs, shift));
    let sticky = match exactness {
        Exactness::Exact => BitWidth(0),
        Exactness::Inexact => BitWidth(1),
    };
    let exponent = lhs
        .exponent
        .0
        .checked_sub(rhs.exponent.0)
        .map(Scale)
        .ok_or(DyadicError::ExponentOutOfRange)?
        .lowered(shift)?
        .lowered(sticky)?;
    return Ok(Unrounded { mantissa, exponent });
}

/// The integer quotient of a widened dividend on the carrier, with its
/// sticky bit.
///
/// # Specification
/// - requires: neither term is zero.
/// - ensures: returns `trunc(lhs · 2^shift / rhs)` and [`Exactness::Exact`]
///   when the division leaves no remainder. Otherwise returns twice that
///   quotient plus the sign of the exact quotient, and [`Exactness::Inexact`].
/// - panics: none.
/// - intension: allocates the widened dividend, the quotient and the remainder.
///
/// # Adequacy
/// - hypothesis: L2 — wide operands through [`Dyadic::div`], held to the
///   oracle.
/// - witness: `tests::oracle::quotient_is_the_directed_neighbour`
#[spec(requires: lhs.sign() != Sign::Zero && rhs.sign() != Sign::Zero)]
fn carried_quotient(
    lhs: Term<'_>,
    rhs: Term<'_>,
    shift: BitWidth,
) -> (Wide, Exactness)
{
    let dividend = lhs.signed_big().shl(shift.0);
    let divisor = rhs.signed_big();
    let quotient = (&dividend).div(&divisor);
    if dividend.rem(&divisor).sign() == num_bigint::Sign::NoSign {
        return (Wide::Large(quotient), Exactness::Exact);
    }
    let sticky = if lhs.sign() == rhs.sign() {
        BigInt::from(1_u8)
    }
    else {
        BigInt::from(-1_i8)
    };
    return (
        Wide::Large(quotient.shl(1_u8).add(sticky)),
        Exactness::Inexact,
    );
}

/// The exact order of two terms.
///
/// # Specification
/// - ensures: orders the denoted values.
/// - panics: none.
/// - intension: the signs decide first, then the top bits. Only magnitudes with
///   one top bit are aligned, and their exponents then differ by the difference
///   of their widths, so the shift is below the wider width.
///
/// # Adequacy
/// - hypothesis: L2 — held to the oracle's cross multiplication over pairs that
///   often share a top bit.
/// - witness: `tests::oracle::order_is_the_rational_order`
/// - witness: `tests::dyadic::order_crosses_the_carriers`
#[spec(ensures: |ref result| *result != Ordering::Equal || lhs.sign() == rhs.sign())]
#[inline]
fn compare(
    lhs: Term<'_>,
    rhs: Term<'_>,
) -> Ordering
{
    let lhs_sign = lhs.sign();
    let rhs_sign = rhs.sign();
    if lhs_sign != rhs_sign {
        return lhs_sign.cmp(&rhs_sign);
    }
    if lhs_sign == Sign::Zero {
        return Ordering::Equal;
    }
    let lhs_width = lhs.width();
    let rhs_width = rhs.width();
    // An exponent fits an `i64` and a width a `u64`, so these sums are exact.
    let lhs_top = i128::from(lhs.exponent.0).saturating_add(i128::from(lhs_width.0));
    let rhs_top = i128::from(rhs.exponent.0).saturating_add(i128::from(rhs_width.0));
    let magnitude = if lhs_top == rhs_top {
        let shift = BitWidth(lhs_width.0.abs_diff(rhs_width.0));
        let (left, right) = if lhs_width <= rhs_width {
            (lhs.magnitude().shifted_up(shift), rhs.magnitude())
        }
        else {
            (lhs.magnitude(), rhs.magnitude().shifted_up(shift))
        };
        left.compare(&right)
    }
    else {
        lhs_top.cmp(&rhs_top)
    };
    return match lhs_sign {
        Sign::Negative => magnitude.reverse(),
        Sign::Zero | Sign::Positive => magnitude,
    };
}

/// An intermediate integer: inline while it fits an `i128`, otherwise on the
/// carrier.
#[derive(Clone, Debug)]
enum Wide
{
    /// An inline integer.
    Small(i128),
    /// An integer on the carrier.
    Large(BigInt),
}

impl Wide
{
    /// The sign.
    ///
    /// # Specification
    /// - ensures: returns the sign of the integer.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — through every rounding, held to the oracle.
    /// - witness: `tests::oracle::round_is_the_directed_neighbour_on_the_grid`
    #[spec(ensures: |ref result| (*result == Sign::Zero) == (self.width().0 == 0))]
    #[inline]
    fn sign(&self) -> Sign
    {
        return self.term().sign();
    }

    /// The bit length of the magnitude.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn width(&self) -> BitWidth
    {
        return self.term().width();
    }

    /// A borrowed view at the exponent zero.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn term(&self) -> Term<'_>
    {
        let digits = match *self {
            Self::Small(value) => Digits::Small(value),
            Self::Large(ref value) => Digits::Large(value),
        };
        return Term {
            digits,
            exponent: Scale(0),
            polarity: Polarity::Keep,
        };
    }

    /// The number of trailing zero bits; zero for the integer zero.
    ///
    /// # Specification
    /// - ensures: returns the largest `k` with `2^k` dividing the integer, or
    ///   zero for zero.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every canonical form strips these bits, held to the
    ///   oracle.
    /// - witness: `tests::oracle::canonical_form_denotes_its_parts`
    #[spec(ensures: |ref result| result.0 <= self.width().0)]
    #[inline]
    fn trailing_zeros(&self) -> BitWidth
    {
        return match *self {
            Self::Small(0) => BitWidth(0),
            Self::Small(value) => BitWidth(u64::from(value.trailing_zeros())),
            Self::Large(ref value) => BitWidth(value.trailing_zeros().unwrap_or(0)),
        };
    }

    /// The integer shifted down by `bits`, rounded toward the floor.
    ///
    /// # Specification
    /// - ensures: returns `floor(self / 2^bits)`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every floor and ceiling of a negative value reads the
    ///   floor shift, held to the oracle.
    /// - witness: `tests::oracle::round_is_the_directed_neighbour_on_the_grid`
    #[spec(captures: width = self.width(), ensures: |ref result| result.width() <= width)]
    #[inline]
    fn shifted_down(
        self,
        bits: BitWidth,
    ) -> Self
    {
        return match self {
            Self::Small(value) => match u32::try_from(bits.0)
                .ok()
                .and_then(|shift| value.checked_shr(shift))
            {
                Some(shifted) => Self::Small(shifted),
                None if value < 0 => Self::Small(-1),
                None => Self::Small(0),
            },
            Self::Large(value) => Self::Large(value.shr(bits.0)),
        };
    }

    /// The integer shifted up by `bits`.
    ///
    /// # Specification
    /// - ensures: returns `self · 2^bits`.
    /// - panics: none.
    /// - intension: an inline integer stays inline while the shifted value fits
    ///   an `i128`, and moves to the carrier otherwise.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every aligned sum reads it, held to the oracle;
    ///   generated gaps straddle the inline bound.
    /// - witness: `tests::oracle::sum_and_difference_are_the_directed_neighbours`
    #[spec(captures: sign = self.sign(), ensures: |ref result| result.sign() == sign)]
    #[inline]
    fn shifted_up(
        self,
        bits: BitWidth,
    ) -> Self
    {
        return match self {
            Self::Small(value) => {
                let inline = u32::try_from(bits.0).ok().and_then(|shift| {
                    value
                        .checked_shl(shift)
                        .filter(|&shifted| shifted.checked_shr(shift) == Some(value))
                });
                inline.map_or_else(|| Self::Large(BigInt::from(value).shl(bits.0)), Self::Small)
            },
            Self::Large(value) => Self::Large(value.shl(bits.0)),
        };
    }

    /// The sum of two integers.
    ///
    /// # Specification
    /// - ensures: returns `self + other`.
    /// - panics: none.
    /// - intension: two inline integers add inline unless the sum overflows.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every sum, held to the oracle.
    /// - witness: `tests::oracle::sum_and_difference_are_the_directed_neighbours`
    #[spec(captures: bound = self.width().0.max(other.width().0).saturating_add(1), ensures: |ref result| result.width().0 <= bound)]
    #[inline]
    fn plus(
        self,
        other: Self,
    ) -> Self
    {
        return match (self, other) {
            (Self::Small(left), Self::Small(right)) => left.checked_add(right).map_or_else(
                || Self::Large(BigInt::from(left).add(BigInt::from(right))),
                Self::Small,
            ),
            (Self::Small(left), Self::Large(right)) => Self::Large(right.add(left)),
            (Self::Large(left), Self::Small(right)) => Self::Large(left.add(right)),
            (Self::Large(left), Self::Large(right)) => Self::Large(left.add(right)),
        };
    }

    /// The integer plus one.
    ///
    /// # Specification
    /// - ensures: returns `self + 1`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every inexact ceiling, held to the oracle.
    /// - witness: `tests::oracle::round_is_the_directed_neighbour_on_the_grid`
    #[spec(captures: bound = self.width().0.saturating_add(1), ensures: |ref result| result.width().0 <= bound)]
    #[inline]
    fn incremented(self) -> Self
    {
        return self.plus(Self::Small(1));
    }

    /// The exact order of two integers.
    ///
    /// # Specification
    /// - ensures: orders the two integers.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every aligned comparison, held to the oracle.
    /// - witness: `tests::oracle::order_is_the_rational_order`
    #[spec(ensures: |ref result| *result != Ordering::Equal || self.sign() == other.sign())]
    #[inline]
    fn compare(
        &self,
        other: &Self,
    ) -> Ordering
    {
        return match (self, other) {
            (&Self::Small(left), &Self::Small(right)) => left.cmp(&right),
            (&Self::Small(left), &Self::Large(ref right)) => BigInt::from(left).cmp(right),
            (&Self::Large(ref left), &Self::Small(right)) => left.cmp(&BigInt::from(right)),
            (&Self::Large(ref left), &Self::Large(ref right)) => left.cmp(right),
        };
    }

    /// The integer as a mantissa, inline when it fits an `i64`.
    ///
    /// # Specification
    /// - ensures: returns the same integer, inline exactly when it fits an
    ///   `i64`.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — values beside both `i64` bounds.
    /// - witness: `tests::dyadic::new_keeps_the_i64_boundary_canonical`
    #[spec(ensures: |ref result| match *result { Mantissa::Small(_) => true, Mantissa::Large(ref value) => i64::try_from(value).is_err() })]
    #[inline]
    fn into_mantissa(self) -> Mantissa
    {
        return match self {
            Self::Small(value) => match i64::try_from(value) {
                Ok(small) => Mantissa::Small(small),
                Err(_wide) => Mantissa::Large(BigInt::from(value)),
            },
            Self::Large(value) => match i64::try_from(&value) {
                Ok(small) => Mantissa::Small(small),
                Err(_wide) => Mantissa::Large(value),
            },
        };
    }
}

/// A dyadic before canonical form and rounding: `mantissa · 2^exponent`
/// with an intermediate exponent.
#[derive(Clone, Debug)]
pub(crate) struct Unrounded
{
    /// The integer, not yet odd.
    mantissa: Wide,
    /// The power of two that scales it.
    exponent: Scale,
}

impl Unrounded
{
    /// The sign.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn sign(&self) -> Sign
    {
        return self.mantissa.sign();
    }

    /// The exact zero.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn zero() -> Self
    {
        return Self {
            mantissa: Wide::Small(0),
            exponent: Scale(0),
        };
    }

    /// The exact order of two intermediate values.
    ///
    /// # Specification
    /// - ensures: orders the denoted values.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the interval product picks its endpoints with it,
    ///   held to the oracle.
    /// - witness: `tests::oracle::interval_product_encloses_every_product`
    #[spec(ensures: |ref result| *result != Ordering::Equal || self.sign() == other.sign())]
    #[inline]
    pub(crate) fn compare(
        &self,
        other: &Self,
    ) -> Ordering
    {
        return compare(self.term(), other.term());
    }

    /// A borrowed view.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn term(&self) -> Term<'_>
    {
        let mut term = self.mantissa.term();
        term.exponent = self.exponent;
        return term;
    }

    /// The value in canonical form, with no rounding.
    ///
    /// # Specification
    /// - ensures: returns the canonical dyadic denoting the same value.
    /// - fails: returns [`DyadicError::ExponentOutOfRange`] when the canonical
    ///   exponent does not fit an `i32`.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DyadicError::ExponentOutOfRange`]: the canonical exponent does not
    ///   fit an `i32`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every result passes through it, held to the oracle;
    ///   L3 — the exponent boundary.
    /// - witness: `tests::oracle::canonical_form_denotes_its_parts`
    /// - witness: `tests::dyadic::new_refuses_an_exponent_past_its_range`
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |value| value.form() == Form::Canonical))]
    #[inline]
    fn canonical(self) -> Result<Dyadic, DyadicError>
    {
        if self.mantissa.sign() == Sign::Zero {
            return Ok(Dyadic::ZERO);
        }
        let zeros = self.mantissa.trailing_zeros();
        let exponent = self.exponent.raised(zeros)?.narrowed()?;
        let mantissa = self.mantissa.shifted_down(zeros).into_mantissa();
        return Ok(Dyadic { mantissa, exponent });
    }

    /// The value rounded to `precision` significant bits toward `rounding`.
    ///
    /// # Specification
    /// - ensures: returns the canonical floor or ceiling of the value on the
    ///   grid of `precision` significant bits, exact when the value fits.
    /// - fails: returns [`DyadicError::ExponentOutOfRange`] when the rounded
    ///   exponent does not fit an `i32`.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`DyadicError::ExponentOutOfRange`]: the rounded exponent does not fit
    ///   an `i32`.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the oracle's floor and ceiling on the grid, over
    ///   every precision from one bit upward and values of both signs.
    /// - witness: `tests::oracle::round_is_the_directed_neighbour_on_the_grid`
    #[spec(ensures: |ref result| result.as_ref().map_or(true, |rounded| rounded.value.form() == Form::Canonical && rounded.value.width() <= BitWidth::from(precision)))]
    #[inline]
    pub(crate) fn round(
        self,
        precision: Precision,
        rounding: Rounding,
    ) -> Result<Rounded, DyadicError>
    {
        if self.mantissa.sign() == Sign::Zero {
            return Ok(Rounded {
                value: Dyadic::ZERO,
                exactness: Exactness::Exact,
            });
        }
        // The inline path: the same steps on an `i128`, with no carrier. A
        // step that does not fit falls through to the general path.
        if let Wide::Small(value) = self.mantissa {
            let inline = (|| {
                let zeros = value.trailing_zeros();
                let odd = value.checked_shr(zeros)?;
                let width = i128::BITS.checked_sub(odd.unsigned_abs().leading_zeros())?;
                return match width.checked_sub(precision.0).filter(|&excess| excess > 0) {
                    None => Some((odd, zeros, Exactness::Exact)),
                    Some(excess) => {
                        let floor = odd.checked_shr(excess)?;
                        let quotient = match rounding {
                            Rounding::Floor => floor,
                            Rounding::Ceiling => floor.checked_add(1)?,
                        };
                        let more = quotient.trailing_zeros();
                        let shift = zeros.checked_add(excess)?.checked_add(more)?;
                        Some((quotient.checked_shr(more)?, shift, Exactness::Inexact))
                    },
                };
            })();
            if let Some((mantissa, shift, exactness)) = inline {
                let exponent = self
                    .exponent
                    .raised(BitWidth(u64::from(shift)))?
                    .narrowed()?;
                let mantissa = i64::try_from(mantissa).map_or_else(
                    |_wide| Mantissa::Large(BigInt::from(mantissa)),
                    Mantissa::Small,
                );
                return Ok(Rounded {
                    value: Dyadic { mantissa, exponent },
                    exactness,
                });
            }
        }
        let zeros = self.mantissa.trailing_zeros();
        let exponent = self.exponent.raised(zeros)?;
        let mantissa = self.mantissa.shifted_down(zeros);
        let width = mantissa.width();
        let Some(excess) = width
            .0
            .checked_sub(u64::from(precision.0))
            .filter(|&excess| excess > 0)
        else {
            let value = Self { mantissa, exponent }.canonical()?;
            return Ok(Rounded {
                value,
                exactness: Exactness::Exact,
            });
        };
        let floor = mantissa.shifted_down(BitWidth(excess));
        let quotient = match rounding {
            Rounding::Floor => floor,
            Rounding::Ceiling => floor.incremented(),
        };
        let exponent = exponent.raised(BitWidth(excess))?;
        let value = Self {
            mantissa: quotient,
            exponent,
        }
        .canonical()?;
        return Ok(Rounded {
            value,
            exactness: Exactness::Inexact,
        });
    }
}
