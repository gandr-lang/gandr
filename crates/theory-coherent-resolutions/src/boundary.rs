//! The engine's own boundary wrappers: every budget, index and verdict a
//! signature of this crate crosses, so no signature passes a bare primitive.
//!
//! Each wrapper is transparent and converts with the standard `From` traits
//! both ways, so a primitive is unpacked only where a comparison, an index or
//! a count needs it. The vocabulary is this crate's alone; the substrate keeps
//! its own counts and decisions, which this crate reads rather than restates.

/// Defines a transparent newtype over one primitive with `From` conversions
/// both ways.
macro_rules! wrapper {
    ($(#[$meta:meta])* $vis:vis struct $name:ident($raw:ty);) => {
        $(#[$meta])*
        #[repr(transparent)]
        $vis struct $name($raw);

        impl From<$raw> for $name
        {
            /// Wraps the primitive.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(value: $raw) -> Self
            {
                Self(value)
            }
        }

        impl From<$name> for $raw
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

wrapper! {
    /// The number of rewrite steps one normalization may take.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct NormalizationBudget(usize);
}

wrapper! {
    /// The number of critical pairs one completion run may process.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct CompletionStepBudget(usize);
}

wrapper! {
    /// The number of cells a store may hold before completion declines to
    /// insert another.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct CompletionCellBudget(usize);
}

wrapper! {
    /// The stable key an overlap support assigns a certificate, in insertion
    /// order.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct CertificateIndex(usize);
}

wrapper! {
    /// The zero-based position of one batch in an overlap worklist.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct BatchIndex(usize);
}

wrapper! {
    /// The zero-based position of one overlap within its batch.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct OverlapIndex(usize);
}

wrapper! {
    /// Whether a normalization stopped at its budget with a redex still
    /// pending, rather than at a normal form.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
    pub struct BudgetExhaustion(bool);
}

wrapper! {
    /// Whether a certificate replays: both recorded paths re-execute from the
    /// peak and reach the recorded join.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
    pub struct TraceletReplay(bool);
}

wrapper! {
    /// Whether two certificates denote one transformation: one boundary, and
    /// each replays.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
    pub struct TraceletEquivalence(bool);
}

wrapper! {
    /// Whether two cells, two certificates or two overlaps are independent
    /// under an overlap support: no overlap relates them.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
    pub struct StepIndependence(bool);
}

wrapper! {
    /// Whether a completion run processed its whole worklist rather than
    /// declining.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
    pub struct CompletionStatus(bool);
}
