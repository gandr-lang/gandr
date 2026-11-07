//! The typed refusals of the distributions.

use core::fmt;

use gandr_theory_cellular_sheaves::Rational;
use gandr_theory_cellular_sheaves::SheafError;

/// Why an operation on distributions gives no distribution: a weight past
/// the integers, a set or an event with no weight, or weights that are not a
/// distribution.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProbabilityError
{
    /// A weight, or a sum or a product of weights, passes the 128-bit
    /// integers that a rational holds.
    Overflow,
    /// A uniform distribution over a set with no point.
    Empty,
    /// A weight that is zero or negative.
    NotPositive(Rational),
    /// Weights whose sum is not one: the sum.
    NotNormalised(Rational),
    /// An event of weight zero, on which no distribution conditions.
    NullEvent,
}

impl fmt::Display for ProbabilityError
{
    /// Renders the refusal, with the weight or the sum it concerns.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Overflow => f.write_str("a weight passes the 128-bit integers"),
            Self::Empty => f.write_str("a uniform distribution over no point"),
            Self::NotPositive(weight) => write!(f, "the weight {weight} is not positive"),
            Self::NotNormalised(sum) => write!(f, "the weights sum to {sum}, not to one"),
            Self::NullEvent => f.write_str("an event of weight zero"),
        }
    }
}

impl core::error::Error for ProbabilityError
{
}

/// The weight that exact arithmetic gives, or [`ProbabilityError::Overflow`]:
/// the one refusal of a rational's sum, product and quotient by a positive
/// weight.
///
/// # Specification
/// trivial.
pub fn exact(weight: Result<Rational, SheafError>) -> Result<Rational, ProbabilityError>
{
    weight.map_err(|_past| ProbabilityError::Overflow)
}
