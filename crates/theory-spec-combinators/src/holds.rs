//! The answer a combinator gives to the claim it checks.

/// Whether a combinator's claim holds of the state it was handed.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Holds(bool);

impl From<bool> for Holds
{
    /// Wraps a decision as a combinator's answer.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Clause cost
    /// - bound: constant; wraps the decision it is handed.
    #[inline]
    fn from(holds: bool) -> Self
    {
        Self(holds)
    }
}

impl From<Holds> for bool
{
    /// Unwraps a combinator's answer to the decision a clause reads.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Clause cost
    /// - bound: constant; unwraps the decision.
    #[inline]
    fn from(holds: Holds) -> Self
    {
        holds.0
    }
}
