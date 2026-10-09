//! Named scalars for the crate's signatures.
//!
//! Every count, ordinal and decision that crosses a signature here is a
//! transparent newtype naming its role, so a count of adopted items cannot be
//! passed where a source ordinal is wanted.

/// Defines a transparent `Copy` wrapper with conversions both ways.
macro_rules! copy_wrapper {
    ($(#[$attribute:meta])* $name:ident, $inner:ty) => {
        $(#[$attribute])*
        #[repr(transparent)]
        #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub struct $name($inner);

        impl From<$inner> for $name
        {
            /// Wraps the raw value.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: $inner) -> Self
            {
                Self(value)
            }
        }

        impl From<$name> for $inner
        {
            /// Unwraps the raw value.
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

copy_wrapper!(
    /// The index of an item in its program's source order.
    ItemOrdinal,
    usize
);
copy_wrapper!(
    /// How many items of the same key precede an item in its program.
    Occurrence,
    usize
);
copy_wrapper!(
    /// The index of a node in one content table.
    NodeIndex,
    usize
);
copy_wrapper!(
    /// A number of items, or of steps a resume took over items.
    ItemCount,
    usize
);
copy_wrapper!(
    /// A number of records a checkpoint store holds.
    RecordCount,
    usize
);
copy_wrapper!(
    /// Which submission of a session a match was written in.
    SubmissionOrdinal,
    usize
);
copy_wrapper!(
    /// Which source item of a submission owns a match.
    SourceItemOrdinal,
    usize
);
copy_wrapper!(
    /// Which match of a source item this is, in source order.
    MatchOrdinal,
    usize
);
copy_wrapper!(
    /// Whether a liveness map publishes nothing.
    LivenessEmpty,
    bool
);
