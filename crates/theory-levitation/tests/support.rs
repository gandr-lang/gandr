//! The suites' own vocabulary: a stand-in grade and the counts, indices and
//! verdicts the test harnesses cross, so no harness signature passes a bare
//! primitive.
//!
//! These are the tests' alone. The crate carries no type that only a test
//! reads.

use core::fmt;

/// A stand-in grade vocabulary: the crate is generic over the grade a field
/// carries, and a consumer supplies its own.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Grade
{
    /// The linear grade.
    One,
}

/// Defines a transparent copyable test-side count over `usize`, with `From`
/// both ways and `Display` passthrough.
macro_rules! test_count {
    ($(#[$meta:meta])* $name:ident) => {
        $(#[$meta])*
        #[repr(transparent)]
        #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct $name(usize);

        impl From<usize> for $name
        {
            /// Wraps the primitive.
            ///
            /// # Specification
            /// trivial.
            fn from(value: usize) -> Self
            {
                Self(value)
            }
        }

        impl From<$name> for usize
        {
            /// Unwraps the primitive.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: $name) -> Self
            {
                value.0
            }
        }

        impl fmt::Display for $name
        {
            /// Writes the wrapped number.
            ///
            /// # Specification
            /// trivial.
            fn fmt(
                &self,
                f: &mut fmt::Formatter<'_>,
            ) -> fmt::Result
            {
                self.0.fmt(f)
            }
        }
    };
}

/// Defines a transparent copyable test-side verdict over `bool`, with `From`
/// both ways.
macro_rules! test_verdict {
    ($(#[$meta:meta])* $name:ident) => {
        $(#[$meta])*
        #[repr(transparent)]
        #[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
        pub struct $name(bool);

        impl From<bool> for $name
        {
            /// Wraps the primitive.
            ///
            /// # Specification
            /// trivial.
            fn from(value: bool) -> Self
            {
                Self(value)
            }
        }

        impl From<$name> for bool
        {
            /// Unwraps the primitive.
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

test_count! {
    /// How many samples one direction of a round-trip replay checked.
    RoundTripSampleCount
}

test_count! {
    /// How many replay-inequivalent classes a set of certificates falls into.
    ReplayClassCount
}

test_count! {
    /// A content-addressed slot in the test-side code table.
    CodeSlot
}

test_count! {
    /// How many factors a product object has.
    DescriptorFactorCount
}

test_count! {
    /// A zero-based factor index into a product object.
    DescriptorFactorIndex
}

test_count! {
    /// A zero-based index into a relation's generating faces or a
    /// signature's rule list.
    GeneratorIndex
}

test_count! {
    /// The longest rewrite path a bounded enumeration explores.
    RewriteDepth
}

test_count! {
    /// The value of a unary numeral `Succⁿ(Zero)`.
    NumeralCount
}

test_count! {
    /// How many arguments a free-term application takes.
    TermArity
}

test_count! {
    /// A zero-based index into a cell program's step table.
    StepIndex
}

test_count! {
    /// How many steps the subprogram a cell step roots spans, itself included.
    StepExtent
}

test_verdict! {
    /// Whether both boundaries of a certificate are parameter-free.
    MonomorphicStatus
}

test_verdict! {
    /// Whether every replayed round trip of a certificate held.
    RoundTripStatus
}

test_verdict! {
    /// Whether two certificates over one boundary replay alike.
    ReplayEquivalence
}

test_verdict! {
    /// Whether a pattern matched a ground term.
    PatternMatch
}

test_verdict! {
    /// Whether two loose instances are equal after boundary normalization.
    LooseInstanceEquality
}

test_verdict! {
    /// Whether two cells replay alike over a corpus.
    CellEquivalence
}

test_verdict! {
    /// Whether a description declares an operation of a name.
    SymbolPresence
}
