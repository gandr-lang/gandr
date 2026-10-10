//! The substrate's own boundary wrappers: every count, step and verdict a
//! signature of this crate crosses, so no signature passes a bare primitive.
//!
//! Each wrapper is transparent and converts with the standard `From` traits
//! both ways, so a primitive is unpacked only where a comparison, an index or
//! a count needs it. The vocabulary is this crate's alone: an engine above
//! keeps its own budgets, indices and verdicts.

use anodized::spec;

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
    /// The number of cells a cell store holds.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct CellCount(usize);
}

wrapper! {
    /// Whether a cell store holds no cells.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
    pub struct CellStoreEmptyStatus(bool);
}

wrapper! {
    /// Whether a cell metavariable's `(name, category)` pair occurs exactly
    /// once on the cell's left-hand side.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
    pub struct CellLinearity(bool);
}

wrapper! {
    /// Whether a cell is an invertible joinability certificate rather than a
    /// directed optimization cell.
    ///
    /// Invertibility names the orientation a joinability certificate may be
    /// read in; it is not an undo operation on derivations.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
    pub struct CellInvertibility(bool);
}

wrapper! {
    /// Whether a cell's provenance permits it to fire at a target term.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
    pub struct FiringPermission(bool);
}

wrapper! {
    /// Whether a pattern contains no metavariable.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
    pub struct GroundPatternStatus(bool);
}

wrapper! {
    /// Whether a position is the root position.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
    pub struct PositionRootStatus(bool);
}

wrapper! {
    /// One child-index step of a position path, counted from the left.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct PositionStep(usize);
}

wrapper! {
    /// The number of metavariables a substitution binds, producer and consumer
    /// together.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct SubstitutionBindingCount(usize);
}

wrapper! {
    /// Whether a match, a unification or a binding succeeded.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
    pub struct SubstitutionDecision(bool);
}

wrapper! {
    /// Whether a substitution binds nothing.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
    pub struct SubstitutionEmptyStatus(bool);
}

wrapper! {
    /// The node count of a pattern subtree.
    #[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
    pub struct PatternSize(usize);
}

impl PatternSize
{
    /// The size of a single node.
    pub const ONE: Self = Self(1);

    /// The sum of two node counts.
    ///
    /// # Specification
    /// - ensures: the exact sum whenever it is representable; otherwise
    ///   `usize::MAX`. A count of nodes held in memory never reaches that
    ///   bound, so every sum the crate forms is exact.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — arbitrary node counts admit zero, ordinary sums and
    ///   the representable/saturated boundary at `usize::MAX`. Exact results
    ///   distinguish wrapping, premature saturation and operand loss.
    /// - witness: `boundary::tests::node_counts_saturate_only_at_the_arithmetic_boundaries`
    #[spec(ensures: |ret| ret.0 == self.0.saturating_add(rhs.0))]
    #[inline]
    #[must_use]
    pub const fn saturating_add(
        self,
        rhs: Self,
    ) -> Self
    {
        Self(self.0.saturating_add(rhs.0))
    }

    /// A node count less a smaller one.
    ///
    /// # Specification
    /// - ensures: the exact difference when `rhs` is at most `self`, which
    ///   holds at every use: a subtree's count is subtracted from the count of
    ///   a tree containing it. Otherwise zero.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — arbitrary node counts admit zero, equal operands and
    ///   either operand larger. Exact differences distinguish wrapping,
    ///   reversed subtraction and a strict guard at equality.
    /// - witness: `boundary::tests::node_counts_saturate_only_at_the_arithmetic_boundaries`
    #[spec(ensures: |ret| ret.0 == self.0.saturating_sub(rhs.0))]
    #[inline]
    #[must_use]
    pub const fn saturating_sub(
        self,
        rhs: Self,
    ) -> Self
    {
        Self(self.0.saturating_sub(rhs.0))
    }
}

#[cfg(test)]
mod tests
{
    use super::PatternSize;

    #[test]
    fn node_counts_saturate_only_at_the_arithmetic_boundaries()
    {
        let below_max = usize::MAX.saturating_sub(1);
        for (left, right, sum, difference) in [
            (0, 0, 0, 0),
            (0, 1, 1, 0),
            (7, 3, 10, 4),
            (3, 7, 10, 0),
            (7, 7, 14, 0),
            (usize::MAX, 0, usize::MAX, usize::MAX),
            (below_max, 1, usize::MAX, usize::MAX.saturating_sub(2)),
            (usize::MAX, 1, usize::MAX, below_max),
        ] {
            let left = PatternSize::from(left);
            let right = PatternSize::from(right);
            assert_eq!(PatternSize::from(sum), left.saturating_add(right));
            assert_eq!(PatternSize::from(difference), left.saturating_sub(right));
        }
    }
}
