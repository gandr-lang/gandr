//! Counts and classifications owned by certificate algebra.

/// Maximum candidate compositions admitted by a query.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PathwayCandidateBudget(usize);
impl From<usize> for PathwayCandidateBudget
{
    /// Wraps the domain value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: usize) -> Self
    {
        Self(value)
    }
}
impl From<PathwayCandidateBudget> for usize
{
    /// Unwraps the domain value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: PathwayCandidateBudget) -> Self
    {
        value.0
    }
}

/// Candidate compositions attempted by a query.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PathwayCandidateCount(usize);
impl From<usize> for PathwayCandidateCount
{
    /// Wraps the domain value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: usize) -> Self
    {
        Self(value)
    }
}
impl From<PathwayCandidateCount> for usize
{
    /// Unwraps the domain value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: PathwayCandidateCount) -> Self
    {
        value.0
    }
}

/// Number of transition certificates in a pathway.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PathwayLength(usize);
impl From<usize> for PathwayLength
{
    /// Wraps the domain value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: usize) -> Self
    {
        Self(value)
    }
}
impl From<PathwayLength> for usize
{
    /// Unwraps the domain value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: PathwayLength) -> Self
    {
        value.0
    }
}

/// Maximum pathway length admitted by a query.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PathwayLengthBudget(usize);
impl From<usize> for PathwayLengthBudget
{
    /// Wraps the domain value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: usize) -> Self
    {
        Self(value)
    }
}
impl From<PathwayLengthBudget> for usize
{
    /// Unwraps the domain value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: PathwayLengthBudget) -> Self
    {
        value.0
    }
}

/// Number of events firing the queried target.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TargetEventCount(usize);
impl From<usize> for TargetEventCount
{
    /// Wraps the domain value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: usize) -> Self
    {
        Self(value)
    }
}
impl From<TargetEventCount> for usize
{
    /// Unwraps the domain value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: TargetEventCount) -> Self
    {
        value.0
    }
}

/// Whether an endpoint participates in one flow direction.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct VarianceFlowRole(bool);
impl From<bool> for VarianceFlowRole
{
    /// Wraps the domain value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: bool) -> Self
    {
        Self(value)
    }
}
impl From<VarianceFlowRole> for bool
{
    /// Unwraps the domain value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: VarianceFlowRole) -> Self
    {
        value.0
    }
}

/// Whether a normal form already has a representative.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PathwayCompression(bool);
impl From<bool> for PathwayCompression
{
    /// Wraps the domain value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: bool) -> Self
    {
        Self(value)
    }
}
impl From<PathwayCompression> for bool
{
    /// Unwraps the domain value.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: PathwayCompression) -> Self
    {
        value.0
    }
}
