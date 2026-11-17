//! Named scalars for the crate's signatures.
//!
//! Every index and count that crosses a signature here is a transparent
//! newtype that names its role, so a table index cannot pass where a place of
//! discovery is wanted.

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
    /// The place of an arena node in the order that its item's walk discovers
    /// the arena nodes: one place for each node, where a table index names one
    /// entry for each content.
    Discovery,
    usize
);
copy_wrapper!(
    /// The place of a child among the children of its content node, in the
    /// order that the node lists them.
    ChildPosition,
    usize
);
