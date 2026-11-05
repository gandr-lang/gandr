//! The usage semiring `{0, 1, ω}`: the number of uses of a hypothesis, with
//! the count forgotten past one.
//!
//! A [`Usage`] is zero, one or many uses. Addition joins the uses of two
//! places. Any two uses add to many. Multiplication scales the uses of a part
//! by the uses of its whole. Zero annihilates. One is the unit. The order
//! puts zero and one below many. It keeps zero and one apart. No rule drops
//! or copies a linear hypothesis.
//!
//! A grade is the bound on the uses of its value. [`HoldGrade`] and
//! [`CapabilityGrade`] are each two points of the semiring: one use, or many.
//! A rule that combines two uses of a held value adds them here. It admits
//! the sum only at or below the grade's bound. The law checker of
//! `gandr-theory-ordered-algebras` decides the sixteen laws of the semiring
//! in the suite `tests::grades`.
//!
//! # References
//!
//! - `vault:01a178aa-6e2c-7720-a0bd-c5e1f9c4e08e` — anchor: § quant-counts —
//!   the usage semiring `{0, 1, ω}`, and the count that the two-point grades
//!   forget.
//!
//! [`HoldGrade`]: crate::memory::HoldGrade
//! [`CapabilityGrade`]: crate::effect::capability::CapabilityGrade

use core::cmp::Ordering;

/// The number of uses of a hypothesis: zero, one, or many.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Usage
{
    /// No use.
    Zero,
    /// Exactly one use.
    One,
    /// `ω`: any number of uses, the count forgotten past one.
    Many,
}

impl Usage
{
    /// The uses of two places together: zero adds nothing, and any two uses
    /// are many.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn add(
        self,
        other: Self,
    ) -> Self
    {
        match (self, other) {
            (Self::Zero, sum) | (sum, Self::Zero) => sum,
            (Self::One | Self::Many, Self::One | Self::Many) => Self::Many,
        }
    }

    /// The uses of a part scaled by the uses of its whole: zero annihilates,
    /// one is the unit, and many times many is many.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn multiply(
        self,
        other: Self,
    ) -> Self
    {
        match (self, other) {
            (Self::Zero, _) | (_, Self::Zero) => Self::Zero,
            (Self::One, product) | (product, Self::One) => product,
            (Self::Many, Self::Many) => Self::Many,
        }
    }
}

impl PartialOrd for Usage
{
    /// The order of the semiring. Each usage lies below itself and below
    /// many. Zero and one lie apart.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn partial_cmp(
        &self,
        other: &Self,
    ) -> Option<Ordering>
    {
        match (*self, *other) {
            (left, right) if left == right => Some(Ordering::Equal),
            (_, Self::Many) => Some(Ordering::Less),
            (Self::Many, _) => Some(Ordering::Greater),
            (Self::Zero | Self::One, Self::Zero | Self::One) => None,
        }
    }
}
