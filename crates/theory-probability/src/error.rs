//! The typed refusals of the distributions and of exact inference.

use core::fmt;

use gandr_theory_cellular_sheaves::CoverIndex;
use gandr_theory_cellular_sheaves::Rational;
use gandr_theory_cellular_sheaves::SheafError;
use gandr_theory_cellular_sheaves::Width;

use crate::table::Variable;

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

/// Why inference over a factor graph gives no result: a scope, a table, a
/// tree or an order that is not well formed, or a weight past the carrier.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InferenceError
{
    /// A variable with no value: its arity is zero.
    NoValue(Variable),
    /// A scope or an elimination order names the variable twice.
    Repeated(Variable),
    /// The number of entries of a table passes the machine's integers.
    TooLarge,
    /// A table whose number of weights is not the width of its scope.
    Width
    {
        /// The width of the scope.
        expected: Width,
        /// The number of weights given.
        given: Width,
    },
    /// A variable that the factor graph does not hold.
    Unknown(Variable),
    /// Two arities of one variable that differ.
    Mismatched(Variable),
    /// An elimination order that leaves the variable out.
    NotEliminated(Variable),
    /// Edges that do not make one tree on the cliques.
    NotATree,
    /// The cliques that hold the variable are not connected in the tree.
    RunningIntersection(Variable),
    /// A scope that no clique or member holds whole.
    Uncovered,
    /// An overlap or an edge that names a member past the family.
    NoMember(CoverIndex),
    /// A sum or a product of weights past the elements that the semiring
    /// represents: for the rational instances, past the 128-bit integers.
    Overflow,
}

impl fmt::Display for InferenceError
{
    /// Renders the refusal, with the variable or the widths it concerns.
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
            Self::NoValue(variable) => write!(f, "the variable {variable} has no value"),
            Self::Repeated(variable) => write!(f, "the variable {variable} appears twice"),
            Self::TooLarge => f.write_str("a table has more entries than the integers count"),
            Self::Width { expected, given } => write!(
                f,
                "a table over {} entries has {} weights",
                usize::from(expected),
                usize::from(given)
            ),
            Self::Unknown(variable) => write!(f, "the graph holds no variable {variable}"),
            Self::Mismatched(variable) => write!(f, "the variable {variable} has two arities"),
            Self::NotEliminated(variable) => {
                write!(f, "the order does not eliminate the variable {variable}")
            },
            Self::NotATree => f.write_str("the edges do not make one tree on the cliques"),
            Self::NoMember(member) => {
                write!(f, "the family holds no member {}", usize::from(member))
            },
            Self::RunningIntersection(variable) => write!(
                f,
                "the cliques that hold the variable {variable} are not connected"
            ),
            Self::Uncovered => f.write_str("no clique holds the scope"),
            Self::Overflow => f.write_str("a weight passes the elements of the semiring"),
        }
    }
}

impl core::error::Error for InferenceError
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
