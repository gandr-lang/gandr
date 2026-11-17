//! Exact linear algebra over the rationals: the matrices of the coboundaries
//! and the pull-backs, their ranks, their kernels and their products.
//!
//! Every entry is a rational in lowest terms over 128-bit integers. A
//! coboundary of a sheaf with entry maps has entries in `{-1, 0, 1}`, and the
//! elimination keeps them small, so the integers suffice. An operation past
//! them is refused, never rounded.

use alloc::vec;
use alloc::vec::Vec;
use core::cmp::Ordering;
use core::fmt;
use core::num::NonZeroU128;

use anodized::spec;

use crate::error::SheafError;
use crate::index::Dimension;
use crate::index::Incidence;
use crate::index::Integer;
use crate::index::Slot;

/// A rational number in lowest terms with a positive denominator.
///
/// # Specification
/// - ensures: the numerator and the denominator have no common factor, and the
///   denominator is positive, so two equal numbers have equal fields.
/// - provides: the sum, the product and the quotient, each exact.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is
///   [`Rational::new`]'s, which every operation ends in.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Rational
{
    /// The numerator, which carries the sign.
    numerator: i128,
    /// The denominator, positive.
    denominator: i128,
}

impl Rational
{
    /// The rational one.
    pub const ONE: Self = Self {
        numerator: 1,
        denominator: 1,
    };
    /// The rational zero.
    pub const ZERO: Self = Self {
        numerator: 0,
        denominator: 1,
    };

    /// The sign an incidence gives: one, minus one or zero.
    ///
    /// # Specification
    /// trivial.
    pub(crate) const fn of_incidence(incidence: Incidence) -> Self
    {
        Self {
            numerator: match incidence {
                Incidence::Positive => 1,
                Incidence::Negative => -1,
                Incidence::Zero => 0,
            },
            denominator: 1,
        }
    }

    /// The rational `numerator / denominator`, in lowest terms.
    ///
    /// # Specification
    /// - requires: the denominator is not zero.
    /// - ensures: the exact quotient, with a positive denominator and no common
    ///   factor.
    /// - fails: a zero denominator, or a sign past the integers, is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::Overflow`]: the denominator is zero, or a part is the
    ///   least 128-bit integer, whose sign the integers cannot move.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — two spellings of one number give one value, so a
    ///   factor left in or a sign left below breaks equality.
    /// - witness: `tests::rational::each_spelling_of_a_number_gives_its_lowest_terms`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |value| value.denominator > 0))]
    #[inline]
    pub fn new(
        numerator: Integer,
        denominator: Integer,
    ) -> Result<Self, SheafError>
    {
        Self {
            numerator: i128::from(numerator),
            denominator: i128::from(denominator),
        }
        .normalised()
    }

    /// The numerator, which carries the sign.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn numerator(self) -> Integer
    {
        Integer::from(self.numerator)
    }

    /// The denominator, which is positive.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn denominator(self) -> Integer
    {
        Integer::from(self.denominator)
    }

    /// The same number in lowest terms with a positive denominator.
    ///
    /// # Specification
    /// - requires: the denominator is not zero.
    /// - ensures: the value is unchanged, the denominator is positive, and the
    ///   numerator and the denominator have no common factor.
    /// - fails: a zero denominator, or a value whose lowest terms pass the
    ///   integers, is refused as an overflow.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::Overflow`]: the denominator is zero, or the sign moves
    ///   past the integers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the coboundaries of every level of both towers reduce
    ///   through it, so a factor left in or a sign lost changes a rank.
    /// - witness: `tests::towers::every_level_of_both_towers_has_the_cohomology_of_its_space`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |value| value.denominator > 0))]
    fn normalised(self) -> Result<Self, SheafError>
    {
        let Self {
            numerator,
            denominator,
        } = self;
        if denominator == 0 {
            return Err(SheafError::Overflow);
        }
        let common = i128::from(divisor(
            Integer::from(numerator),
            Integer::from(denominator),
        )?);
        let sign: i128 = if denominator < 0 { -1 } else { 1 };
        let numerator = numerator
            .checked_div(common)
            .and_then(|value| value.checked_mul(sign))
            .ok_or(SheafError::Overflow)?;
        let denominator = denominator
            .checked_div(common)
            .and_then(|value| value.checked_mul(sign))
            .ok_or(SheafError::Overflow)?;
        Ok(Self {
            numerator,
            denominator,
        })
    }

    /// The sum of two rationals, over the least common multiple of the two
    /// denominators.
    ///
    /// # Specification
    /// - ensures: the exact sum, in lowest terms.
    /// - fails: a sum whose numerator or denominator over the least common
    ///   denominator passes the integers is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::Overflow`]: a scaled numerator, their sum or the least
    ///   common denominator passes the integers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the products of the pull-backs and the coboundaries
    ///   of both towers sum signed ones, so a wrong sum breaks a commuting
    ///   square; two weights over `2^64` sum to one, which the product of the
    ///   denominators passes.
    /// - witness: `tests::towers::each_bonding_map_induces_an_isomorphism_on_cohomology`
    /// - witness: `tests::rational::a_result_in_range_is_given_whatever_its_operands`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |value| value.denominator > 0))]
    #[inline]
    pub fn plus(
        self,
        other: Self,
    ) -> Result<Self, SheafError>
    {
        let common = i128::from(divisor(
            Integer::from(self.denominator),
            Integer::from(other.denominator),
        )?);
        let left_scale = other
            .denominator
            .checked_div(common)
            .ok_or(SheafError::Overflow)?;
        let right_scale = self
            .denominator
            .checked_div(common)
            .ok_or(SheafError::Overflow)?;
        let left = self.numerator.checked_mul(left_scale);
        let right = other.numerator.checked_mul(right_scale);
        let numerator = left
            .zip(right)
            .and_then(|(left, right)| left.checked_add(right))
            .ok_or(SheafError::Overflow)?;
        let denominator = self
            .denominator
            .checked_mul(left_scale)
            .ok_or(SheafError::Overflow)?;
        Self {
            numerator,
            denominator,
        }
        .normalised()
    }

    /// The product of two rationals, each numerator first reduced against
    /// the other's denominator.
    ///
    /// # Specification
    /// - ensures: the exact product, in lowest terms.
    /// - fails: a product whose lowest terms pass the integers is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::Overflow`]: the product passes the integers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the elimination scales and subtracts rows through it
    ///   on every level of both towers; a product in range whose plain
    ///   numerator passes the integers is given.
    /// - witness: `tests::towers::every_level_of_both_towers_has_the_cohomology_of_its_space`
    /// - witness: `tests::rational::a_result_in_range_is_given_whatever_its_operands`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |value| value.denominator > 0))]
    #[inline]
    pub fn times(
        self,
        other: Self,
    ) -> Result<Self, SheafError>
    {
        let first = i128::from(divisor(
            Integer::from(self.numerator),
            Integer::from(other.denominator),
        )?);
        let second = i128::from(divisor(
            Integer::from(other.numerator),
            Integer::from(self.denominator),
        )?);
        let reduced = |value: i128, by: i128| value.checked_div(by).ok_or(SheafError::Overflow);
        let numerator = reduced(self.numerator, first)?
            .checked_mul(reduced(other.numerator, second)?)
            .ok_or(SheafError::Overflow)?;
        let denominator = reduced(self.denominator, second)?
            .checked_mul(reduced(other.denominator, first)?)
            .ok_or(SheafError::Overflow)?;
        Self {
            numerator,
            denominator,
        }
        .normalised()
    }

    /// The quotient of two rationals: the product by the reciprocal of
    /// `other`, so the same reduction keeps a quotient in range.
    ///
    /// # Specification
    /// - requires: `other` is not zero.
    /// - ensures: the exact quotient, in lowest terms.
    /// - fails: a zero divisor or a quotient whose lowest terms pass the
    ///   integers is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::Overflow`]: `other` is zero, or the quotient passes the
    ///   integers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the elimination scales each pivot row to one through
    ///   it on every level of both towers.
    /// - witness: `tests::towers::every_level_of_both_towers_has_the_cohomology_of_its_space`
    /// - witness: `tests::rational::the_arithmetic_is_exact_and_refuses_past_the_integers`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |value| value.denominator > 0))]
    #[inline]
    pub fn over(
        self,
        other: Self,
    ) -> Result<Self, SheafError>
    {
        let reciprocal = Self {
            numerator: other.denominator,
            denominator: other.numerator,
        }
        .normalised()?;
        self.times(reciprocal)
    }

    /// The difference of two rationals.
    ///
    /// # Specification
    /// - ensures: the exact difference, in lowest terms.
    /// - fails: a difference past the integers is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::Overflow`]: the difference passes the integers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the elimination subtracts the pivot row through it on
    ///   every level of both towers.
    /// - witness: `tests::towers::every_level_of_both_towers_has_the_cohomology_of_its_space`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |value| value.denominator > 0))]
    fn minus(
        self,
        other: Self,
    ) -> Result<Self, SheafError>
    {
        let negated = other.numerator.checked_neg().ok_or(SheafError::Overflow)?;
        self.plus(Self {
            numerator: negated,
            denominator: other.denominator,
        })
    }
}

/// The greatest common divisor of the magnitudes of `left` and `right`, by
/// Euclid's algorithm: positive whenever either is not zero.
///
/// # Specification
/// - ensures: the greatest integer that divides both, zero only when both are
///   zero.
/// - fails: a magnitude past the integers, that of the least 128-bit integer,
///   is refused.
/// - panics: none.
///
/// # Errors
/// - [`SheafError::Overflow`]: `left` or `right` is the least 128-bit integer.
///
/// # Adequacy
/// - hypothesis: L2 — every rational is reduced through it, so a divisor too
///   small leaves a factor in and two spellings of one number differ.
/// - witness: `tests::rational::each_spelling_of_a_number_gives_its_lowest_terms`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |common| i128::from(*common) >= 0))]
fn divisor(
    left: Integer,
    right: Integer,
) -> Result<Integer, SheafError>
{
    let mut larger = i128::from(left).checked_abs().ok_or(SheafError::Overflow)?;
    let mut smaller = i128::from(right)
        .checked_abs()
        .ok_or(SheafError::Overflow)?;
    while smaller != 0 {
        let rest = larger.checked_rem(smaller).ok_or(SheafError::Overflow)?;
        larger = smaller;
        smaller = rest;
    }
    Ok(Integer::from(larger))
}

impl fmt::Display for Rational
{
    /// Renders the number as `numerator/denominator`, or as the numerator
    /// alone when the denominator is one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        if self.denominator == 1 {
            return write!(f, "{}", self.numerator);
        }
        write!(f, "{}/{}", self.numerator, self.denominator)
    }
}

impl PartialOrd for Rational
{
    /// The order of the numbers, which is total.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn partial_cmp(
        &self,
        other: &Self,
    ) -> Option<Ordering>
    {
        Some(self.cmp(other))
    }
}

impl Ord for Rational
{
    /// The order of the numbers: the signs first, then the magnitudes, with
    /// no product formed, so no comparison overflows.
    ///
    /// # Specification
    /// - ensures: `Equal` exactly when the two numbers are equal.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — pairs of each sign, an equal pair in two spellings,
    ///   and a pair whose cross products pass the integers separate a sign read
    ///   wrong and a product that overflows.
    /// - witness: `tests::rational::the_order_of_rationals_is_the_order_of_the_numbers`
    #[spec(ensures: |ret| (ret == Ordering::Equal) == (self == other))]
    #[inline]
    fn cmp(
        &self,
        other: &Self,
    ) -> Ordering
    {
        match (self.numerator.is_negative(), other.numerator.is_negative()) {
            (true, false) => Ordering::Less,
            (false, true) => Ordering::Greater,
            (false, false) => magnitudes(self.magnitude(), other.magnitude()),
            (true, true) => magnitudes(other.magnitude(), self.magnitude()),
        }
    }
}

impl Rational
{
    /// The absolute values of the numerator and of the denominator.
    ///
    /// # Specification
    /// trivial.
    fn magnitude(self) -> Magnitude
    {
        Magnitude {
            numerator: self.numerator.unsigned_abs(),
            // The denominator is positive by the invariant of `Rational`.
            denominator: NonZeroU128::new(self.denominator.unsigned_abs())
                .unwrap_or(NonZeroU128::MIN),
        }
    }
}

/// The absolute value of a rational: a numerator and a positive denominator.
#[derive(Clone, Copy, Debug)]
struct Magnitude
{
    /// The absolute value of the numerator.
    numerator: u128,
    /// The absolute value of the denominator, which is positive.
    denominator: NonZeroU128,
}

/// The order of two magnitudes as numbers, by their continued fractions: the
/// integer parts first, then the reciprocals of the two fractional parts with
/// the sides swapped. Each step divides, so no product is formed.
///
/// # Specification
/// - ensures: the order of the two quotients, which equals the order of the
///   cross products wherever those fit the integers.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — a pair whose cross products pass the integers, and pairs
///   that differ in the integer part and in the fractional part only.
/// - witness: `tests::rational::the_order_of_rationals_is_the_order_of_the_numbers`
#[spec(ensures: |ret| left.numerator.checked_mul(right.denominator.get()).zip(right.numerator.checked_mul(left.denominator.get())).is_none_or(|(first, second)| ret == first.cmp(&second)))]
fn magnitudes(
    left: Magnitude,
    right: Magnitude,
) -> Ordering
{
    let (mut first, mut second) = (left, right);
    loop {
        let whole = first.numerator.div_euclid(first.denominator.get());
        let other = second.numerator.div_euclid(second.denominator.get());
        if whole != other {
            return whole.cmp(&other);
        }
        let part = NonZeroU128::new(first.numerator.rem_euclid(first.denominator.get()));
        let other_part = NonZeroU128::new(second.numerator.rem_euclid(second.denominator.get()));
        match (part, other_part) {
            (None, None) => return Ordering::Equal,
            (None, Some(_)) => return Ordering::Less,
            (Some(_), None) => return Ordering::Greater,
            // `part / first.denominator` against `other_part /
            // second.denominator`: the reciprocals compare the other way, so
            // the sides swap.
            (Some(part), Some(other_part)) => {
                (first, second) = (
                    Magnitude {
                        numerator: second.denominator.get(),
                        denominator: other_part,
                    },
                    Magnitude {
                        numerator: first.denominator.get(),
                        denominator: part,
                    },
                );
            },
        }
    }
}

/// A matrix over the rationals, row by row.
///
/// # Specification
/// - ensures: the entries hold one value for each row and each column.
/// - provides: the shape and the rank.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is
///   [`Matrix::zero`]'s, which makes every matrix.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Matrix
{
    /// The number of rows.
    rows: Dimension,
    /// The number of columns.
    columns: Dimension,
    /// The entries, row by row.
    entries: Vec<Rational>,
}

impl Matrix
{
    /// The matrix of zeros with `rows` rows and `columns` columns.
    ///
    /// # Specification
    /// - ensures: one zero entry for each row and each column.
    /// - fails: a shape whose size passes the machine word is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::Overflow`]: the number of entries passes the machine
    ///   word.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the circle's level of four points has a coboundary of
    ///   four rows and four columns.
    /// - witness: `tests::towers::the_circles_level_of_four_points_has_the_rationals_in_degrees_zero_and_one`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |matrix| matrix.rows == rows && matrix.columns == columns))]
    pub(crate) fn zero(
        rows: Dimension,
        columns: Dimension,
    ) -> Result<Self, SheafError>
    {
        let size = usize::from(rows)
            .checked_mul(usize::from(columns))
            .ok_or(SheafError::Overflow)?;
        Ok(Self {
            rows,
            columns,
            entries: vec![Rational::ZERO; size],
        })
    }

    /// The matrix with `rows` rows and `columns` columns whose entries, row by
    /// row, are `entries`.
    ///
    /// # Specification
    /// - ensures: the entry at each row and column is the one `entries` gives
    ///   at that place, row by row.
    /// - fails: another number of entries than the rows times the columns is
    ///   refused by the shape.
    /// - panics: none.
    /// - intension: `entries` is read once, up to one entry past the shape.
    ///
    /// # Errors
    /// - [`SheafError::MatrixEntries`]: `entries` holds another number of
    ///   entries than the rows times the columns.
    /// - [`SheafError::Overflow`]: the number of entries passes the machine
    ///   word.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the restriction of the projective line's chart into
    ///   the overlap is admitted with its entries in place, and a matrix one
    ///   entry short and one entry long are each refused by its shape.
    /// - witness: `tests::linear::the_projective_line_s_twist_by_minus_two_has_one_class_in_degree_one`
    /// - witness: `tests::linear::a_matrix_of_another_number_of_entries_is_refused`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |matrix| matrix.rows == rows && matrix.columns == columns))]
    #[inline]
    pub fn new<Entries>(
        rows: Dimension,
        columns: Dimension,
        entries: Entries,
    ) -> Result<Self, SheafError>
    where
        Entries: IntoIterator<Item = Rational>,
    {
        let size = usize::from(rows)
            .checked_mul(usize::from(columns))
            .ok_or(SheafError::Overflow)?;
        let mut held = Vec::with_capacity(size);
        for entry in entries {
            if held.len() == size {
                return Err(SheafError::MatrixEntries { rows, columns });
            }
            held.push(entry);
        }
        if held.len() != size {
            return Err(SheafError::MatrixEntries { rows, columns });
        }
        Ok(Self {
            rows,
            columns,
            entries: held,
        })
    }

    /// The identity matrix on `dimension` rows and columns.
    ///
    /// # Specification
    /// - ensures: one on the diagonal and zero elsewhere.
    /// - fails: a shape whose size passes the machine word is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::Overflow`]: the number of entries passes the machine
    ///   word.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the top degree of each level of both towers takes
    ///   every cochain as a cocycle through it, so a lost diagonal entry lowers
    ///   the rank of the induced map in degree one.
    /// - witness: `tests::towers::each_bonding_map_induces_an_isomorphism_on_cohomology`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |matrix| matrix.rows == dimension && matrix.columns == dimension))]
    pub(crate) fn identity(dimension: Dimension) -> Result<Self, SheafError>
    {
        let mut matrix = Self::zero(dimension, dimension)?;
        for diagonal in 0 .. usize::from(dimension) {
            let at = Slot::from(diagonal);
            matrix.add(at, at, Rational::ONE)?;
        }
        Ok(matrix)
    }

    /// The number of rows.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn rows(&self) -> Dimension
    {
        self.rows
    }

    /// The number of columns.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn columns(&self) -> Dimension
    {
        self.columns
    }

    /// The place of an entry in the row-by-row list.
    ///
    /// # Specification
    /// - ensures: the place lies inside the entries.
    /// - fails: a row or a column past the shape is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::ShapeMismatch`]: the row or the column lies past the
    ///   shape, unreachable for the matrices the crate builds.
    /// - [`SheafError::Overflow`]: the place passes the machine word.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every coboundary of both towers is written through
    ///   it, so a transposed place breaks a rank.
    /// - witness: `tests::towers::every_level_of_both_towers_has_the_cohomology_of_its_space`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |place| usize::from(*place) < self.entries.len()))]
    fn place(
        &self,
        row: Slot,
        column: Slot,
    ) -> Result<Slot, SheafError>
    {
        if usize::from(row) >= usize::from(self.rows)
            || usize::from(column) >= usize::from(self.columns)
        {
            return Err(SheafError::ShapeMismatch);
        }
        usize::from(row)
            .checked_mul(usize::from(self.columns))
            .and_then(|start| start.checked_add(usize::from(column)))
            .map(Slot::from)
            .ok_or(SheafError::Overflow)
    }

    /// The entry at `row` and `column`.
    ///
    /// # Specification
    /// - provides: the entry.
    /// - fails: a row or a column past the shape is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::ShapeMismatch`]: the row or the column lies past the
    ///   shape.
    /// - [`SheafError::Overflow`]: the place passes the machine word.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every product of both towers reads through it.
    /// - witness: `tests::towers::each_bonding_map_induces_an_isomorphism_on_cohomology`
    #[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(SheafError::ShapeMismatch | SheafError::Overflow)))]
    pub(crate) fn at(
        &self,
        row: Slot,
        column: Slot,
    ) -> Result<Rational, SheafError>
    {
        let place = self.place(row, column)?;
        self.entries
            .get(usize::from(place))
            .copied()
            .ok_or(SheafError::ShapeMismatch)
    }

    /// Adds `value` to the entry at `row` and `column`.
    ///
    /// # Specification
    /// - ensures: the entry grows by `value`, and no other entry changes.
    /// - fails: a row or a column past the shape, or a sum past the integers,
    ///   is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::ShapeMismatch`]: the row or the column lies past the
    ///   shape.
    /// - [`SheafError::Overflow`]: the sum passes the integers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — every coboundary and pull-back of both towers is
    ///   written through it.
    /// - witness: `tests::towers::every_level_of_both_towers_has_the_cohomology_of_its_space`
    #[spec(ensures: |ref ret| ret.is_ok() || matches!(*ret, Err(SheafError::ShapeMismatch | SheafError::Overflow)))]
    pub(crate) fn add(
        &mut self,
        row: Slot,
        column: Slot,
        value: Rational,
    ) -> Result<(), SheafError>
    {
        let place = self.place(row, column)?;
        let entry = self
            .entries
            .get_mut(usize::from(place))
            .ok_or(SheafError::ShapeMismatch)?;
        let sum = entry.plus(value)?;
        *entry = sum;
        Ok(())
    }

    /// The product of this matrix and `right`.
    ///
    /// # Specification
    /// - requires: this matrix has as many columns as `right` has rows.
    /// - ensures: the exact product, with this matrix's rows and `right`'s
    ///   columns.
    /// - fails: shapes that do not chain, or a sum past the integers, are
    ///   refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::ShapeMismatch`]: the shapes do not chain.
    /// - [`SheafError::Overflow`]: a sum passes the integers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — both composites of each commuting square of both
    ///   towers, so a wrong product refuses a bonding map that commutes.
    /// - witness: `tests::towers::each_bonding_map_induces_an_isomorphism_on_cohomology`
    /// - witness: `tests::towers::a_bonding_map_that_breaks_a_square_is_refused`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |product| product.rows == self.rows && product.columns == right.columns))]
    pub(crate) fn product(
        &self,
        right: &Self,
    ) -> Result<Self, SheafError>
    {
        if self.columns != right.rows {
            return Err(SheafError::ShapeMismatch);
        }
        let mut product = Self::zero(self.rows, right.columns)?;
        for row in 0 .. usize::from(self.rows) {
            for through in 0 .. usize::from(self.columns) {
                let scale = self.at(Slot::from(row), Slot::from(through))?;
                if scale == Rational::ZERO {
                    continue;
                }
                for column in 0 .. usize::from(right.columns) {
                    let value = right.at(Slot::from(through), Slot::from(column))?;
                    let term = scale.times(value)?;
                    product.add(Slot::from(row), Slot::from(column), term)?;
                }
            }
        }
        Ok(product)
    }

    /// This matrix with the columns of `right` after its own.
    ///
    /// # Specification
    /// - requires: both matrices have the same rows.
    /// - ensures: the rows of this matrix, each followed by the same row of
    ///   `right`.
    /// - fails: matrices with other numbers of rows are refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::ShapeMismatch`]: the numbers of rows differ.
    /// - [`SheafError::Overflow`]: the width passes the machine word.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the image of each induced map of both towers is the
    ///   rank of the coboundaries beside the pulled-back cocycles.
    /// - witness: `tests::towers::each_bonding_map_induces_an_isomorphism_on_cohomology`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |beside| beside.rows == self.rows))]
    pub(crate) fn beside(
        &self,
        right: &Self,
    ) -> Result<Self, SheafError>
    {
        if self.rows != right.rows {
            return Err(SheafError::ShapeMismatch);
        }
        let columns = usize::from(self.columns)
            .checked_add(usize::from(right.columns))
            .ok_or(SheafError::Overflow)?;
        let mut beside = Self::zero(self.rows, Dimension::from(columns))?;
        for row in 0 .. usize::from(self.rows) {
            for column in 0 .. usize::from(self.columns) {
                let value = self.at(Slot::from(row), Slot::from(column))?;
                beside.add(Slot::from(row), Slot::from(column), value)?;
            }
            for column in 0 .. usize::from(right.columns) {
                let value = right.at(Slot::from(row), Slot::from(column))?;
                let shifted = usize::from(self.columns)
                    .checked_add(column)
                    .ok_or(SheafError::Overflow)?;
                beside.add(Slot::from(row), Slot::from(shifted), value)?;
            }
        }
        Ok(beside)
    }

    /// The reduced row echelon form: the rows that hold a pivot, each scaled
    /// so that its pivot is one, with zeros above and below each pivot, and
    /// the column of each pivot.
    ///
    /// # Specification
    /// - ensures: one pivot column for each returned row, increasing.
    /// - fails: elimination past the integers is refused.
    /// - panics: none.
    /// - intension: Gauss–Jordan elimination over the rationals, the first row
    ///   with a nonzero entry in each column taken as its pivot.
    ///
    /// # Errors
    /// - [`SheafError::Overflow`]: an entry passes the integers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the rank and the kernel of every coboundary of both
    ///   towers read from it; L3 — the circle's level of four points has a
    ///   coboundary of rank three.
    /// - witness: `tests::towers::the_circles_level_of_four_points_has_the_rationals_in_degrees_zero_and_one`
    /// - witness: `tests::towers::every_level_of_both_towers_has_the_cohomology_of_its_space`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |&(ref rows, ref pivots)| rows.len() == pivots.len()))]
    fn echelon(&self) -> Result<(Vec<Vec<Rational>>, Vec<Slot>), SheafError>
    {
        let width = usize::from(self.columns);
        let mut rows: Vec<Vec<Rational>> = Vec::with_capacity(usize::from(self.rows));
        if width > 0 {
            rows.extend(self.entries.chunks(width).map(<[Rational]>::to_vec));
        }
        let mut pivots = Vec::new();
        for column in 0 .. width {
            let found = pivots.len();
            let Some(offset) = rows.iter().skip(found).position(|row| {
                row.get(column)
                    .is_some_and(|value| *value != Rational::ZERO)
            })
            else {
                continue;
            };
            rows.swap(found, found.saturating_add(offset));
            let (before, rest) = rows.split_at_mut(found);
            let Some((pivot, after)) = rest.split_first_mut()
            else {
                return Err(SheafError::ShapeMismatch);
            };
            let lead = pivot
                .get(column)
                .copied()
                .ok_or(SheafError::ShapeMismatch)?;
            for value in pivot.iter_mut() {
                let scaled = value.over(lead)?;
                *value = scaled;
            }
            for other in before.iter_mut().chain(after.iter_mut()) {
                let factor = other
                    .get(column)
                    .copied()
                    .ok_or(SheafError::ShapeMismatch)?;
                if factor == Rational::ZERO {
                    continue;
                }
                for (value, &from_pivot) in other.iter_mut().zip(pivot.iter()) {
                    let term = factor.times(from_pivot)?;
                    let reduced = value.minus(term)?;
                    *value = reduced;
                }
            }
            pivots.push(Slot::from(column));
        }
        rows.truncate(pivots.len());
        Ok((rows, pivots))
    }

    /// The rank over the rationals.
    ///
    /// # Specification
    /// - ensures: the rank is at most the rows and at most the columns.
    /// - fails: elimination past the integers is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`SheafError::Overflow`]: an entry passes the integers.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the circle's level of four points has a coboundary of
    ///   rank three, one less than its size; L2 — every level of both towers,
    ///   whose cohomology reads from the ranks.
    /// - witness: `tests::towers::the_circles_level_of_four_points_has_the_rationals_in_degrees_zero_and_one`
    /// - witness: `tests::towers::every_level_of_both_towers_has_the_cohomology_of_its_space`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |rank| *rank <= self.rows && *rank <= self.columns))]
    #[inline]
    pub fn rank(&self) -> Result<Dimension, SheafError>
    {
        let (_, pivots) = self.echelon()?;
        Ok(Dimension::from(pivots.len()))
    }

    /// A basis of the kernel, one column for each column without a pivot.
    ///
    /// # Specification
    /// - ensures: the columns are independent, each maps to zero, and their
    ///   number is the columns less the rank.
    /// - fails: elimination past the integers is refused.
    /// - panics: none.
    /// - intension: the basis vector of a free column is one there, the negated
    ///   reduced entry of that column at each pivot column, and zero elsewhere.
    ///
    /// # Errors
    /// - [`SheafError::Overflow`]: an entry passes the integers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — each bonding map of both towers pulls back the
    ///   coarser level's cocycles through it, so a vector outside the kernel or
    ///   a lost one changes the rank of an induced map.
    /// - witness: `tests::towers::each_bonding_map_induces_an_isomorphism_on_cohomology`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |kernel| kernel.rows == self.columns))]
    pub(crate) fn kernel(&self) -> Result<Self, SheafError>
    {
        let (rows, pivots) = self.echelon()?;
        let width = usize::from(self.columns);
        let mut free: Vec<Slot> = Vec::with_capacity(width.saturating_sub(pivots.len()));
        let mut next_pivot = pivots.iter().copied().peekable();
        for column in (0 .. width).map(Slot::from) {
            if next_pivot.next_if_eq(&column).is_none() {
                free.push(column);
            }
        }
        let mut kernel = Self::zero(self.columns, Dimension::from(free.len()))?;
        for (vector, &column) in free.iter().enumerate() {
            kernel.add(column, Slot::from(vector), Rational::ONE)?;
            for (row, &pivot) in rows.iter().zip(&pivots) {
                let value = row
                    .get(usize::from(column))
                    .copied()
                    .ok_or(SheafError::ShapeMismatch)?;
                let negated = Rational::ZERO.minus(value)?;
                kernel.add(pivot, Slot::from(vector), negated)?;
            }
        }
        Ok(kernel)
    }
}
