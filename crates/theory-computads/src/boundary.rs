//! The crate's own boundary wrappers: every index, count and verdict a
//! signature of this crate crosses, so no signature passes a bare primitive.
//!
//! Each wrapper is transparent and converts with the standard `From` traits,
//! so a primitive is unpacked only where a comparison or a count needs it. The
//! vocabulary is this crate's alone: a wrapper of another crate a signature
//! here mentions is that crate's, named by a dependent's own manifest, and
//! nothing is re-exported.
//!
//! # Boundary wrappers
//!
//! The crate owns the nominal wrappers its own signatures cross: the indices
//! its reports carry (`DeclinedFaceIndex`, `DeclinedOpIndex`), the counts its
//! refusals carry (`OperationInputCount`, `ConstructorCount`,
//! `RedexOccurrenceCount`), the verdict on a rule's growth from an earlier one
//! (`RuleGrowth`), and private verdicts. A wrapper of another crate a
//! signature here mentions is that crate's.

use core::fmt;

/// Defines a transparent copyable newtype over one `usize`, with `From`
/// conversions both ways and `Display` passthrough.
macro_rules! count_wrapper {
    ($(#[$meta:meta])* $vis:vis struct $name:ident;) => {
        $(#[$meta])*
        #[repr(transparent)]
        #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
        $vis struct $name(usize);

        impl From<usize> for $name
        {
            /// Wraps the primitive.
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
            #[inline]
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

/// Defines a transparent copyable newtype over one `bool` verdict, with `From`
/// conversions both ways.
macro_rules! verdict_wrapper {
    ($(#[$meta:meta])* $vis:vis struct $name:ident;) => {
        $(#[$meta])*
        #[repr(transparent)]
        #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
        $vis struct $name(bool);

        impl From<bool> for $name
        {
            /// Wraps the primitive.
            ///
            /// # Specification
            /// trivial.
            #[inline]
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

count_wrapper! {
    /// The index of a declined rule face in its description's `rules`.
    pub struct DeclinedFaceIndex;
}

count_wrapper! {
    /// The index of an admitted rule face in its description's `rules`.
    pub struct AdmittedFaceIndex;
}

count_wrapper! {
    /// The index of a declined operation in its description's `opers`.
    pub struct DeclinedOpIndex;
}

count_wrapper! {
    /// How many input ports an operation declares: `|A|` of its arity.
    pub struct OperationInputCount;
}

count_wrapper! {
    /// How many constructors a description declares.
    pub struct ConstructorCount;
}

count_wrapper! {
    /// How many redex occurrences a circuit body unfolds to.
    pub struct RedexOccurrenceCount;
}

verdict_wrapper! {
    /// Whether a face states that an operation inverts a constructor.
    pub struct InverseFacePresence;
}

verdict_wrapper! {
    /// Whether a rule is an earlier one with one subterm wrapped in a fixed
    /// context, the rest renamed.
    pub struct RuleGrowth;
}

verdict_wrapper! {
    /// Whether some rule's left side matches a term at some node.
    pub struct Reducibility;
}

verdict_wrapper! {
    /// Whether one term spells another up to renaming its variables one to
    /// one.
    pub struct Renaming;
}
