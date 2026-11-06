//! The typed refusals of the collapse.

use core::fmt;

use crate::collapse::Budget;

/// Why a collapse gives no answer: the caller's complex refuses, or the walk
/// of the gradient goes past its budget.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MorseError<Fault>
{
    /// The caller's complex or scheme refuses with its own fault.
    Complex(Fault),
    /// The walk of the gradient reaches more redundant cells than this budget.
    PastBudget(Budget),
}

impl<Fault> From<Fault> for MorseError<Fault>
{
    /// Wraps the caller's fault.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(fault: Fault) -> Self
    {
        Self::Complex(fault)
    }
}

impl<Fault> fmt::Display for MorseError<Fault>
where
    Fault: fmt::Display,
{
    /// Renders the refusal: the caller's fault, or the budget the walk passes.
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
            Self::Complex(ref fault) => write!(f, "the complex refused: {fault}"),
            Self::PastBudget(budget) => write!(
                f,
                "the walk of the gradient reaches more than {} redundant cells",
                usize::from(budget)
            ),
        }
    }
}

impl<Fault> core::error::Error for MorseError<Fault>
where
    Fault: core::error::Error + 'static,
{
    /// The caller's fault, when the complex refuses.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)>
    {
        match *self {
            Self::Complex(ref fault) => Some(fault),
            Self::PastBudget(_) => None,
        }
    }
}
