//! Every refusal of the e-graph.

use core::fmt;

use gandr_theory_coherent_resolutions::LawvereError;
use gandr_theory_coherent_resolutions::TermPlace;
use gandr_theory_coherent_resolutions::Variable;

use crate::egraph::EquationPlace;

/// Why the e-graph gives no answer.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum EGraphError
{
    /// The term table refuses a place or a substitution.
    Table(LawvereError),
    /// The e-graph holds no term at this place.
    Unheld(TermPlace),
    /// The two terms lie in different classes, so no explanation joins them.
    Apart(TermPlace, TermPlace),
    /// The left side of the equation at this place is a variable, so it
    /// matches every term.
    VariableLeft(EquationPlace),
    /// The right side of the equation at this place holds this variable, and
    /// its left side does not.
    Unbound(EquationPlace, Variable),
    /// No equation stands at this place.
    UnknownEquation(EquationPlace),
    /// An instance of the equation at this place gives a number of values
    /// other than the number of its variables.
    Values(EquationPlace),
    /// A congruence in the proof forest needs an explanation of its children
    /// that the forest does not give. The forest is corrupt.
    Unexplained(TermPlace, TermPlace),
}

impl From<LawvereError> for EGraphError
{
    /// The table's refusal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(error: LawvereError) -> Self
    {
        Self::Table(error)
    }
}

impl fmt::Display for EGraphError
{
    /// The refusal in words.
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
            Self::Table(error) => write!(f, "the term table refuses: {error}"),
            Self::Unheld(place) => write!(
                f,
                "the e-graph holds no term at place {}",
                usize::from(place)
            ),
            Self::Apart(left, right) => write!(
                f,
                "the terms at places {} and {} lie in different classes",
                usize::from(left),
                usize::from(right)
            ),
            Self::VariableLeft(equation) => write!(
                f,
                "the left side of equation {} is a variable",
                usize::from(equation)
            ),
            Self::Unbound(equation, variable) => write!(
                f,
                "the right side of equation {} holds the variable {}, and its left side does not",
                usize::from(equation),
                usize::from(variable)
            ),
            Self::UnknownEquation(equation) => {
                write!(f, "no equation stands at place {}", usize::from(equation))
            },
            Self::Values(equation) => write!(
                f,
                "an instance of equation {} gives the wrong number of values",
                usize::from(equation)
            ),
            Self::Unexplained(left, right) => write!(
                f,
                "the proof forest gives no explanation of places {} and {}",
                usize::from(left),
                usize::from(right)
            ),
        }
    }
}

impl core::error::Error for EGraphError
{
}
