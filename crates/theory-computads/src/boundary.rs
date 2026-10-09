//! The crate's own boundary wrappers: every index, count and verdict a
//! signature of this crate crosses, so no signature passes a bare primitive.
//!
//! Each wrapper is transparent and converts with the standard `From` traits,
//! so a primitive is unpacked only where a comparison or a count needs it. The
//! vocabulary is this crate's alone: a wrapper of another crate a signature
//! here mentions is that crate's, named by a dependent's own manifest, and
//! nothing is re-exported.

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
