//! Indices, cardinalities, and typed failures of the face calculus.

use core::fmt;

/// Defines a nominal index with conversions only at standard trait boundaries.
macro_rules! index {
    ($name:ident, $doc:literal) => {
        #[doc = $doc]
        #[repr(transparent)]
        #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct $name(pub usize);

        impl From<usize> for $name
        {
            /// Wraps an index.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: usize) -> Self
            {
                Self(value)
            }
        }
        impl From<$name> for usize
        {
            /// Reads an index.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: $name) -> Self
            {
                value.0
            }
        }
    };
}

index!(Point, "A point of a finite carrier.");
index!(PointCount, "The cardinality of a finite carrier.");
index!(Dimension, "A bridge coordinate in an affine context.");
index!(
    DimensionCount,
    "The number of coordinates in an affine context."
);
index!(Variable, "A coordinate in a mixed shape context.");
index!(NodeId, "A formula node's position in its flat table.");
index!(Case, "A case in a coordinate's finite observation domain.");

/// A malformed input or invalid evidence, never a negative entailment result.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ShapeError
{
    /// A finite point lies outside its carrier.
    PointOutside(Point),
    /// Finite subshapes have different ambient cardinalities.
    DifferentAmbient,
    /// The source of an inclusion contains a point outside its target.
    NotIncluded(Point),
    /// A source coordinate is out of range.
    DimensionOutside(Dimension),
    /// A context map attempts contraction of a source coordinate.
    Contraction(Dimension),
    /// Affine context maps do not compose.
    DifferentContext,
    /// A formula has no root or a child is not earlier than its parent.
    MalformedFormula,
    /// A formula names a variable outside the context.
    VariableOutside(Variable),
    /// An atom or assignment has the wrong shape at a coordinate.
    WrongShape(Variable),
    /// A supplied assignment has the wrong length.
    AssignmentLength,
    /// A countermodel contains an unassigned coordinate.
    IncompleteAssignment(Variable),
    /// The alleged countermodel does not satisfy premise and refute conclusion.
    NotCountermodel,
    /// A derivation is truncated, has extra steps, splits an assigned
    /// coordinate, or uses a leaf rule whose condition is false.
    InvalidDerivation,
    /// A case index is outside a coordinate's domain.
    CaseOutside,
}

impl fmt::Display for ShapeError
{
    /// Renders a stable failure category and any offending coordinate.
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
            | Self::PointOutside(point) => write!(f, "finite point {} outside carrier", point.0),
            | Self::DifferentAmbient => f.write_str("different finite ambient carriers"),
            | Self::NotIncluded(point) => write!(f, "point {} outside inclusion target", point.0),
            | Self::DimensionOutside(dim) => {
                write!(f, "bridge coordinate {} outside source", dim.0)
            },
            | Self::Contraction(dim) => write!(f, "bridge coordinate {} copied", dim.0),
            | Self::DifferentContext => f.write_str("affine context maps do not compose"),
            | Self::MalformedFormula => f.write_str("malformed formula table"),
            | Self::VariableOutside(var) => write!(f, "variable {} outside context", var.0),
            | Self::WrongShape(var) => write!(f, "wrong shape at variable {}", var.0),
            | Self::AssignmentLength => f.write_str("assignment length differs from context"),
            | Self::IncompleteAssignment(var) => write!(f, "variable {} unassigned", var.0),
            | Self::NotCountermodel => f.write_str("assignment is not a countermodel"),
            | Self::InvalidDerivation => f.write_str("invalid entailment derivation"),
            | Self::CaseOutside => f.write_str("case outside observation domain"),
        }
    }
}

impl core::error::Error for ShapeError
{
}
