//! Two instances over exact dyadic reals: the max-plus semiring, and the
//! Lawvere quantale of extended non-negative distances under the reverse
//! order.
//!
//! Both carriers are infinite, so each instance holds the elements a check
//! generates. A sum of two dyadics is exact up to the widest precision the
//! dyadic crate offers, and a sum past it refuses with [`Outside`].

use alloc::vec::Vec;
use core::fmt;

use anodized::spec;
use gandr_theory_exact_reals::Dyadic;
use gandr_theory_exact_reals::Exactness;
use gandr_theory_exact_reals::Precision;
use gandr_theory_exact_reals::Rounding;
use gandr_theory_exact_reals::Sign;

use crate::signature::Carrier;
use crate::signature::Comparison;
use crate::signature::InstanceName;
use crate::signature::OrderedSemiring;
use crate::signature::Outside;

/// The exact sum of two dyadics.
///
/// # Specification
/// - ensures: the result is the exact sum.
/// - fails: a sum that needs more than the widest precision is refused.
/// - panics: none.
///
/// # Errors
/// - [`Outside`]: the exact sum needs more bits than [`Precision::MAX`], or its
///   exponent leaves the dyadic crate's range.
///
/// # Adequacy
/// - hypothesis: L2 — sums of halves and of whole numbers against the max-plus
///   and Lawvere laws separate a rounded sum from an exact one.
/// - witness: `tests::laws::the_max_plus_semiring_passes_every_law`
/// - witness: `tests::laws::the_lawvere_quantale_passes_every_law`
#[spec(ensures: |ref ret| ret.is_ok() || *ret == Err(Outside))]
fn exact_sum(
    left: &Dyadic,
    right: &Dyadic,
) -> Result<Dyadic, Outside>
{
    let rounded = left
        .add(right, Precision::MAX, Rounding::Floor)
        .map_err(|_overflow| Outside)?;
    match rounded.exactness() {
        Exactness::Exact => Ok(rounded.into_value()),
        Exactness::Inexact => Err(Outside),
    }
}

/// An element of the max-plus semiring: an exact dyadic, or `−∞`.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum MaxPlus
{
    /// `−∞`, the unit of the maximum and the zero of the sum.
    NegativeInfinity,
    /// A finite dyadic.
    Finite(Dyadic),
}

/// The max-plus semiring over exact dyadics with `−∞`: the maximum adds, the
/// sum multiplies, and the order is the order of the numbers.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Tropical
{
    /// The elements a check reads.
    generated: Vec<MaxPlus>,
}

impl Tropical
{
    /// The semiring whose check reads `generated`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn generated(generated: Vec<MaxPlus>) -> Self
    {
        Self { generated }
    }
}

impl OrderedSemiring for Tropical
{
    type Element = MaxPlus;

    /// `max-plus`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn name(&self) -> InstanceName
    {
        InstanceName::from("max-plus")
    }

    /// The generated elements.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn carrier(&self) -> Carrier<'_, MaxPlus>
    {
        Carrier::Generated(&self.generated)
    }

    /// `−∞`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn zero(&self) -> MaxPlus
    {
        MaxPlus::NegativeInfinity
    }

    /// The dyadic zero.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn one(&self) -> MaxPlus
    {
        MaxPlus::Finite(Dyadic::ZERO)
    }

    /// The maximum.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn add(
        &self,
        left: &MaxPlus,
        right: &MaxPlus,
    ) -> Result<MaxPlus, Outside>
    {
        Ok(match self.compare(left, right) {
            Comparison::Below => right.clone(),
            Comparison::NotBelow => left.clone(),
        })
    }

    /// The exact sum, `−∞` absorbing.
    ///
    /// # Specification
    /// - ensures: `−∞` with either side `−∞`.
    /// - fails: a sum past the widest precision is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Outside`]: the exact sum lies past the represented dyadics.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — annihilation and distribution over generated elements
    ///   with `−∞` separate a lost absorption.
    /// - witness: `tests::laws::the_max_plus_semiring_passes_every_law`
    #[spec(ensures: |ref ret| !matches!((left, right), (&MaxPlus::NegativeInfinity, _) | (_, &MaxPlus::NegativeInfinity)) || *ret == Ok(MaxPlus::NegativeInfinity))]
    #[inline]
    fn multiply(
        &self,
        left: &MaxPlus,
        right: &MaxPlus,
    ) -> Result<MaxPlus, Outside>
    {
        match (left, right) {
            (&MaxPlus::Finite(ref left), &MaxPlus::Finite(ref right)) => {
                Ok(MaxPlus::Finite(exact_sum(left, right)?))
            },
            _ => Ok(MaxPlus::NegativeInfinity),
        }
    }

    /// The order of the numbers, `−∞` least.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn compare(
        &self,
        lower: &MaxPlus,
        upper: &MaxPlus,
    ) -> Comparison
    {
        match (lower, upper) {
            (&MaxPlus::NegativeInfinity, _) => Comparison::Below,
            (&MaxPlus::Finite(_), &MaxPlus::NegativeInfinity) => Comparison::NotBelow,
            (&MaxPlus::Finite(ref lower), &MaxPlus::Finite(ref upper)) => {
                if lower <= upper {
                    Comparison::Below
                }
                else {
                    Comparison::NotBelow
                }
            },
        }
    }
}

/// A dyadic below zero, which no distance is.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NegativeDistance(Dyadic);

impl NegativeDistance
{
    /// The refused dyadic.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn value(&self) -> &Dyadic
    {
        &self.0
    }
}

impl fmt::Display for NegativeDistance
{
    /// States the refusal. The refused dyadic is [`NegativeDistance::value`].
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str("a distance lies below zero")
    }
}

impl core::error::Error for NegativeDistance
{
}

/// An element of the Lawvere quantale: an exact non-negative dyadic, or `∞`.
///
/// # Specification
/// - ensures: a finite distance is at or above zero.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is the constructor's,
///   which checks it.
///
/// # Adequacy
/// - hypothesis: L3 — a negative dyadic is refused by its value.
/// - witness: `tests::laws::a_negative_distance_is_refused`
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Distance
{
    /// The distance, `None` for `∞`.
    value: Option<Dyadic>,
}

impl Distance
{
    /// `∞`, the unit of the minimum and the zero of the sum.
    pub const INFINITY: Self = Self { value: None };

    /// The finite distance `value`.
    ///
    /// # Specification
    /// - ensures: the distance holds `value`.
    /// - fails: a dyadic below zero is refused by its value.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`NegativeDistance`]: `value` lies below zero.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — zero is admitted and minus one is refused.
    /// - witness: `tests::laws::a_negative_distance_is_refused`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |distance| distance.value.is_some()))]
    #[inline]
    pub fn finite(value: Dyadic) -> Result<Self, NegativeDistance>
    {
        if value.sign() == Sign::Negative {
            return Err(NegativeDistance(value));
        }
        Ok(Self { value: Some(value) })
    }

    /// The finite value, or `None` for `∞`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn value(&self) -> Option<&Dyadic>
    {
        self.value.as_ref()
    }
}

/// The Lawvere quantale of extended non-negative dyadics: the minimum adds,
/// the sum multiplies, and the order is the reverse of the numbers', so `∞`
/// is least.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Lawvere
{
    /// The elements a check reads.
    generated: Vec<Distance>,
}

impl Lawvere
{
    /// The quantale whose check reads `generated`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn generated(generated: Vec<Distance>) -> Self
    {
        Self { generated }
    }
}

impl OrderedSemiring for Lawvere
{
    type Element = Distance;

    /// `lawvere`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn name(&self) -> InstanceName
    {
        InstanceName::from("lawvere")
    }

    /// The generated elements.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn carrier(&self) -> Carrier<'_, Distance>
    {
        Carrier::Generated(&self.generated)
    }

    /// `∞`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn zero(&self) -> Distance
    {
        Distance::INFINITY
    }

    /// The distance zero.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn one(&self) -> Distance
    {
        Distance {
            value: Some(Dyadic::ZERO),
        }
    }

    /// The minimum, which is the join of the reverse order.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn add(
        &self,
        left: &Distance,
        right: &Distance,
    ) -> Result<Distance, Outside>
    {
        Ok(match self.compare(left, right) {
            Comparison::Below => right.clone(),
            Comparison::NotBelow => left.clone(),
        })
    }

    /// The exact sum, `∞` absorbing.
    ///
    /// # Specification
    /// - ensures: `∞` with either side `∞`.
    /// - fails: a sum past the widest precision is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Outside`]: the exact sum lies past the represented dyadics.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — annihilation and distribution over generated elements
    ///   with `∞` separate a lost absorption.
    /// - witness: `tests::laws::the_lawvere_quantale_passes_every_law`
    #[spec(ensures: |ref ret| (left.value.is_some() && right.value.is_some()) || *ret == Ok(Distance::INFINITY))]
    #[inline]
    fn multiply(
        &self,
        left: &Distance,
        right: &Distance,
    ) -> Result<Distance, Outside>
    {
        match (left.value.as_ref(), right.value.as_ref()) {
            (Some(left), Some(right)) => Ok(Distance {
                value: Some(exact_sum(left, right)?),
            }),
            _ => Ok(Distance::INFINITY),
        }
    }

    /// The reverse of the numbers' order, `∞` least.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn compare(
        &self,
        lower: &Distance,
        upper: &Distance,
    ) -> Comparison
    {
        match (lower.value.as_ref(), upper.value.as_ref()) {
            (None, _) => Comparison::Below,
            (Some(_), None) => Comparison::NotBelow,
            (Some(lower), Some(upper)) => {
                if lower >= upper {
                    Comparison::Below
                }
                else {
                    Comparison::NotBelow
                }
            },
        }
    }
}
