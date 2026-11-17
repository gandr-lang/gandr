//! Two ordered semirings over the non-negative rationals: the probability
//! semiring, whose sum gives marginals, and the max-times semiring, whose sum
//! gives the most likely assignment.
//!
//! The max-times semiring is the tropical semiring read through `−log`: the
//! maximum adds and the product multiplies. The max-plus instance of
//! `theory-ordered-algebras` holds dyadics, and the logarithm of a rational
//! weight such as `1/5` is no dyadic, so the rational form keeps each weight
//! exact. A sum or a product past the 128-bit integers is refused with
//! [`Outside`].

use alloc::vec::Vec;

use gandr_theory_cellular_sheaves::Rational;
use gandr_theory_ordered_algebras::Carrier;
use gandr_theory_ordered_algebras::Comparison;
use gandr_theory_ordered_algebras::InstanceName;
use gandr_theory_ordered_algebras::OrderedSemiring;
use gandr_theory_ordered_algebras::Outside;

/// The order of the rationals as a [`Comparison`].
///
/// # Specification
/// trivial.
fn ordered(
    lower: Rational,
    upper: Rational,
) -> Comparison
{
    if lower <= upper {
        Comparison::Below
    }
    else {
        Comparison::NotBelow
    }
}

/// The probability semiring over the non-negative rationals: the sum adds,
/// the product multiplies, and the order is the order of the numbers.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Probability
{
    /// The elements a check reads.
    generated: Vec<Rational>,
}

impl Probability
{
    /// The semiring whose law check reads `generated`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn generated(generated: Vec<Rational>) -> Self
    {
        Self { generated }
    }
}

impl OrderedSemiring for Probability
{
    type Element = Rational;

    /// `probability`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn name(&self) -> InstanceName
    {
        InstanceName::from("probability")
    }

    /// The generated elements.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn carrier(&self) -> Carrier<'_, Rational>
    {
        Carrier::Generated(&self.generated)
    }

    /// Zero.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn zero(&self) -> Rational
    {
        Rational::ZERO
    }

    /// One.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn one(&self) -> Rational
    {
        Rational::ONE
    }

    /// The exact sum, or [`Outside`] past the 128-bit integers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn add(
        &self,
        left: &Rational,
        right: &Rational,
    ) -> Result<Rational, Outside>
    {
        left.plus(*right).map_err(|_overflow| Outside)
    }

    /// The exact product, or [`Outside`] past the 128-bit integers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn multiply(
        &self,
        left: &Rational,
        right: &Rational,
    ) -> Result<Rational, Outside>
    {
        left.times(*right).map_err(|_overflow| Outside)
    }

    /// The order of the numbers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn compare(
        &self,
        lower: &Rational,
        upper: &Rational,
    ) -> Comparison
    {
        ordered(*lower, *upper)
    }
}

/// The max-times semiring over the non-negative rationals: the maximum adds,
/// the product multiplies, and the order is the order of the numbers. It is
/// the tropical semiring read through `−log`.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct MaxTimes
{
    /// The elements a check reads.
    generated: Vec<Rational>,
}

impl MaxTimes
{
    /// The semiring whose law check reads `generated`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn generated(generated: Vec<Rational>) -> Self
    {
        Self { generated }
    }
}

impl OrderedSemiring for MaxTimes
{
    type Element = Rational;

    /// `max-times`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn name(&self) -> InstanceName
    {
        InstanceName::from("max-times")
    }

    /// The generated elements.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn carrier(&self) -> Carrier<'_, Rational>
    {
        Carrier::Generated(&self.generated)
    }

    /// Zero, the least non-negative rational.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn zero(&self) -> Rational
    {
        Rational::ZERO
    }

    /// One.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn one(&self) -> Rational
    {
        Rational::ONE
    }

    /// The greater of the two.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn add(
        &self,
        left: &Rational,
        right: &Rational,
    ) -> Result<Rational, Outside>
    {
        Ok(*left.max(right))
    }

    /// The exact product, or [`Outside`] past the 128-bit integers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn multiply(
        &self,
        left: &Rational,
        right: &Rational,
    ) -> Result<Rational, Outside>
    {
        left.times(*right).map_err(|_overflow| Outside)
    }

    /// The order of the numbers.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn compare(
        &self,
        lower: &Rational,
        upper: &Rational,
    ) -> Comparison
    {
        ordered(*lower, *upper)
    }
}
