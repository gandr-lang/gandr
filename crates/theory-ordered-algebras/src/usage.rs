//! The usage semiring `{0, 1, ω}`: the number of uses of a hypothesis, with
//! the count forgotten past one.
//!
//! A [`Usage`] is zero, one or many uses. Addition joins the uses of two
//! places. Any two uses add to many. Multiplication scales the uses of a part
//! by the uses of its whole. Zero annihilates. One is the unit. The order
//! puts zero and one below many. It keeps zero and one apart. No rule drops
//! or copies a linear hypothesis.
//!
//! A grade of the core language is the bound on the uses of its value. The
//! access rules of the core checker add two uses of a held value here, and
//! admit the sum only at or below the grade's bound. [`Usages`] is the
//! semiring's instance on its whole carrier. Each operation of the instance
//! calls the `const fn` of [`Usage`], so the law checker decides the
//! operations that the access rules run.
//!
//! # References
//!
//! - `vault:01a178aa-6e2c-7720-a0bd-c5e1f9c4e08e` — anchor: § quant-counts —
//!   the usage semiring `{0, 1, ω}`, and the count that the two-point grades
//!   forget.
//! - `Wood-2024-framework_semiringannotated_type_systems` — newest: one
//!   calculus annotated by any semiring, whose instance at `{0, 1, ω}` is the
//!   dual-context calculus that [`Usage`] gives the access rules.

use core::cmp::Ordering;

use crate::signature::Carrier;
use crate::signature::Comparison;
use crate::signature::InstanceName;
use crate::signature::OrderedSemiring;
use crate::signature::Outside;

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

/// The usage semiring on its three points, the whole carrier.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub struct Usages;

impl OrderedSemiring for Usages
{
    type Element = Usage;

    /// `usages`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn name(&self) -> InstanceName
    {
        InstanceName::from("usages")
    }

    /// Zero, one and many: the whole carrier.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn carrier(&self) -> Carrier<'_, Usage>
    {
        Carrier::Whole(&[Usage::Zero, Usage::One, Usage::Many])
    }

    /// No use.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn zero(&self) -> Usage
    {
        Usage::Zero
    }

    /// One use.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn one(&self) -> Usage
    {
        Usage::One
    }

    /// [`Usage::add`], which never leaves the carrier.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn add(
        &self,
        left: &Usage,
        right: &Usage,
    ) -> Result<Usage, Outside>
    {
        Ok(left.add(*right))
    }

    /// [`Usage::multiply`], which never leaves the carrier.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn multiply(
        &self,
        left: &Usage,
        right: &Usage,
    ) -> Result<Usage, Outside>
    {
        Ok(left.multiply(*right))
    }

    /// The order of [`Usage`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn compare(
        &self,
        lower: &Usage,
        upper: &Usage,
    ) -> Comparison
    {
        if lower <= upper {
            Comparison::Below
        }
        else {
            Comparison::NotBelow
        }
    }
}
