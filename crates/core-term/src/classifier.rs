//! The classifier vocabulary: what a type's own type is, as a sort and a
//! level.
//!
//! # A classifier is a ground sort and a level
//!
//! Every type has exactly one [`Classifier`]: the universe it inhabits, read
//! as the [`GroundSort`] of the family and the level within it. `Type[+, l]`
//! classifies the value types at level `l` and `Type[-, l]` the computation
//! types; both universes are themselves value types, so each lives in
//! `Type[+, l + 1]`.
//!
//! # A universe's sort may be a parameter, and formation refuses it by name
//!
//! A universe node carries a [`Sort`] rather than a ground sort, so a
//! declaration generic over its sort is representable before it is checkable:
//! the classifier of `Type[s, l]` with `s` a parameter has no ground reading,
//! and formation answers it with a named refusal rather than a guess. No
//! producer writes a parameter sort until the prenex sort binders land; the
//! variant is the one place their absence is stated.

use gandr_kernel_strata::Level;
use gandr_kernel_term::GroundSort;

/// The position of a sort binder in its declaration's prenex sort telescope.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SortParameter(u32);

impl From<u32> for SortParameter
{
    /// Wraps a raw telescope position as a sort parameter.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(position: u32) -> Self
    {
        Self(position)
    }
}

impl From<SortParameter> for u32
{
    /// Unwraps a sort parameter to its raw telescope position.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(parameter: SortParameter) -> Self
    {
        parameter.0
    }
}

/// The sort a universe node is indexed by: a ground sort, or a parameter of
/// the declaration that has no ground reading yet.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Sort
{
    /// One of the two ground families.
    Ground(GroundSort),
    /// A sort parameter of the enclosing declaration.
    Parameter(SortParameter),
}

impl From<GroundSort> for Sort
{
    /// A ground sort as a universe's sort.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(sort: GroundSort) -> Self
    {
        Self::Ground(sort)
    }
}

/// The universe a type inhabits: its ground sort and its level.
///
/// A classifier is what formation answers for a type, and it is total over the
/// formed types: every type that forms has exactly one. A universe's own
/// classifier is the value sort one level up.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Classifier
{
    /// The family the type belongs to.
    pub sort: GroundSort,
    /// The level within that family.
    pub level: Level,
}
