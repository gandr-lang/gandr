//! The exact amplitudes of Clifford+T circuits: the ring `ℤ[1/√2, i]`, its
//! real subring `ℤ[1/√2]`, and an instance of each under the discrete order.
//!
//! An amplitude is `(a + b√2 + (c + d√2)i) / 2^k`, with integers `a`, `b`, `c`
//! and `d` and the least `k`. The four numbers `1`, `√2`, `i` and `i√2` are
//! linearly independent over the rationals. So the least `k` makes the form
//! canonical: two amplitudes are equal exactly when their forms are equal.
//!
//! Each operation is exact. A coefficient, or a partial product or sum of
//! coefficients, past the 128-bit integers is refused with [`Outside`], and
//! no result is rounded.

use alloc::vec::Vec;

use anodized::spec;

use crate::signature::Carrier;
use crate::signature::CommutativeRing;
use crate::signature::Comparison;
use crate::signature::InstanceName;
use crate::signature::OrderedSemiring;
use crate::signature::Outside;

/// An integer coefficient of an amplitude.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Coefficient(i128);

impl From<i128> for Coefficient
{
    /// The coefficient `value`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(value: i128) -> Self
    {
        Self(value)
    }
}

impl From<Coefficient> for i128
{
    /// The coefficient's integer.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(coefficient: Coefficient) -> Self
    {
        coefficient.0
    }
}

/// The exponent `k` of an amplitude's denominator `2^k`.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Scale(u32);

impl From<u32> for Scale
{
    /// The scale `k`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(exponent: u32) -> Self
    {
        Self(exponent)
    }
}

impl From<Scale> for u32
{
    /// The scale's exponent.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(scale: Scale) -> Self
    {
        scale.0
    }
}

/// The integer `rational + irrational · √2` of `ℤ[√2]`.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
struct Root2
{
    /// The rational part.
    rational: i128,
    /// The coefficient of `√2`.
    irrational: i128,
}

impl Root2
{
    /// Zero.
    const ZERO: Self = Self {
        rational: 0,
        irrational: 0,
    };

    /// The exact sum.
    ///
    /// # Specification
    /// - ensures: the sum of the two parts.
    /// - fails: a part of the sum past the 128-bit integers is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Outside`]: a part of the sum lies past the 128-bit integers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the ring laws on generated amplitudes separate a lost
    ///   or doubled part; L3 — a sum past the integers is refused.
    /// - witness: `tests::amplitudes::the_amplitudes_pass_every_ring_law`
    /// - witness: `tests::amplitudes::a_coefficient_past_128_bits_is_refused`
    #[spec(ensures: |ref ret| ret.as_ref().map_or_else(
        |_| self.rational.checked_add(other.rational).is_none() || self.irrational.checked_add(other.irrational).is_none(),
        |sum| sum.rational.wrapping_sub(other.rational) == self.rational && sum.irrational.wrapping_sub(other.irrational) == self.irrational,
    ))]
    fn add(
        self,
        other: Self,
    ) -> Result<Self, Outside>
    {
        Ok(Self {
            rational: self.rational.checked_add(other.rational).ok_or(Outside)?,
            irrational: self
                .irrational
                .checked_add(other.irrational)
                .ok_or(Outside)?,
        })
    }

    /// The exact difference.
    ///
    /// # Specification
    /// - ensures: the difference of the two parts.
    /// - fails: a part of the difference past the 128-bit integers is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Outside`]: a part of the difference lies past the 128-bit integers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the ring laws read the real part of a product, which
    ///   subtracts.
    /// - witness: `tests::amplitudes::the_amplitudes_pass_every_ring_law`
    #[spec(ensures: |ref ret| ret.as_ref().map_or_else(
        |_| self.rational.checked_sub(other.rational).is_none() || self.irrational.checked_sub(other.irrational).is_none(),
        |difference| difference.rational.wrapping_add(other.rational) == self.rational && difference.irrational.wrapping_add(other.irrational) == self.irrational,
    ))]
    fn subtract(
        self,
        other: Self,
    ) -> Result<Self, Outside>
    {
        Ok(Self {
            rational: self.rational.checked_sub(other.rational).ok_or(Outside)?,
            irrational: self
                .irrational
                .checked_sub(other.irrational)
                .ok_or(Outside)?,
        })
    }

    /// The exact negation.
    ///
    /// # Specification
    /// - ensures: both parts negated.
    /// - fails: the least 128-bit integer has no negation, so it is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Outside`]: a part is the least 128-bit integer.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the additive inverse law reads each negation.
    /// - witness: `tests::amplitudes::the_amplitudes_pass_every_ring_law`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(
        self.rational == i128::MIN || self.irrational == i128::MIN,
        |negation| negation.rational.wrapping_add(self.rational) == 0 && negation.irrational.wrapping_add(self.irrational) == 0,
    ))]
    fn negate(self) -> Result<Self, Outside>
    {
        Ok(Self {
            rational: self.rational.checked_neg().ok_or(Outside)?,
            irrational: self.irrational.checked_neg().ok_or(Outside)?,
        })
    }

    /// The exact product, `(a + b√2)(c + d√2) = (ac + 2bd) + (ad + bc)√2`.
    ///
    /// # Specification
    /// - ensures: the product of the two integers of `ℤ[√2]`.
    /// - fails: a product or a sum of parts past the 128-bit integers is
    ///   refused.
    /// - panics: none.
    /// - intension: four products of parts and one doubling.
    ///
    /// # Errors
    /// - [`Outside`]: a product or a sum of parts lies past the 128-bit
    ///   integers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the ring laws and the gates' unitarity separate a
    ///   lost doubling or a crossed part.
    /// - witness: `tests::amplitudes::the_amplitudes_pass_every_ring_law`
    /// - witness: `tests::gates::each_gate_is_unitary`
    #[spec(ensures: |ref ret| {
        let norm = |value: &Self| value.rational.wrapping_mul(value.rational).wrapping_sub(value.irrational.wrapping_mul(value.irrational).wrapping_mul(2));
        ret.as_ref().map_or(true, |product| norm(product) == norm(&self).wrapping_mul(norm(&other)))
    })]
    fn multiply(
        self,
        other: Self,
    ) -> Result<Self, Outside>
    {
        let product = |left: i128, right: i128| left.checked_mul(right).ok_or(Outside);
        let doubled = product(product(self.irrational, other.irrational)?, 2)?;
        let rational = product(self.rational, other.rational)?
            .checked_add(doubled)
            .ok_or(Outside)?;
        let irrational = product(self.rational, other.irrational)?
            .checked_add(product(self.irrational, other.rational)?)
            .ok_or(Outside)?;
        Ok(Self {
            rational,
            irrational,
        })
    }

    /// `self · 2^shift`.
    ///
    /// # Specification
    /// - ensures: both parts multiplied by `2^shift`; zero at any shift.
    /// - fails: a part past the 128-bit integers is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Outside`]: a scaled part lies past the 128-bit integers.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a sum of two amplitudes at different scales lifts one
    ///   of them; a lift past the integers is refused.
    /// - witness: `tests::amplitudes::a_scaled_form_reduces_to_its_own`
    /// - witness: `tests::amplitudes::a_coefficient_past_128_bits_is_refused`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |lifted| if shift.0 >= 128 {
        *lifted == Self::ZERO
    } else {
        lifted.rational.wrapping_shr(shift.0) == self.rational && lifted.irrational.wrapping_shr(shift.0) == self.irrational
    }))]
    fn scaled(
        self,
        shift: Scale,
    ) -> Result<Self, Outside>
    {
        if self == Self::ZERO || shift.0 == 0 {
            return Ok(self);
        }
        let factor = 1_i128
            .checked_shl(shift.0)
            .filter(|factor| *factor > 0)
            .ok_or(Outside)?;
        Ok(Self {
            rational: self.rational.checked_mul(factor).ok_or(Outside)?,
            irrational: self.irrational.checked_mul(factor).ok_or(Outside)?,
        })
    }

    /// Both parts halved. The caller halves even parts only, so the halves are
    /// exact.
    ///
    /// # Specification
    /// - requires: both parts are even.
    /// - ensures: both parts divided by two.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a form with every coefficient even reduces to its
    ///   value's least form.
    /// - witness: `tests::amplitudes::a_scaled_form_reduces_to_its_own`
    #[spec(requires: (self.rational | self.irrational) & 1 == 0)]
    fn halved(self) -> Self
    {
        Self {
            rational: self.rational.wrapping_shr(1),
            irrational: self.irrational.wrapping_shr(1),
        }
    }

    /// The square, `(a + b√2)² = (a² + 2b²) + 2ab√2`.
    ///
    /// # Specification
    /// - ensures: the product of the integer with itself.
    /// - fails: a part past the 128-bit integers is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Outside`]: a part of the square lies past the 128-bit integers.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the squared moduli of the state of `H T H` on `|0⟩`
    ///   are `(2 + √2)/4` and `(2 − √2)/4`.
    /// - witness: `tests::amplitudes::the_squared_moduli_of_h_t_h_sum_to_one`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |square| square.rational >= 0 && square.irrational & 1 == 0))]
    fn squared(self) -> Result<Self, Outside>
    {
        self.multiply(self)
    }
}

/// The amplitude `(real + imaginary · i) / 2^scale` at its least scale.
///
/// # Specification
/// - ensures: the same value at the least scale that keeps every coefficient an
///   integer; zero at scale zero.
/// - panics: none.
/// - intension: at most 127 halvings, since a non-zero 128-bit integer has at
///   most 126 trailing zeros.
///
/// # Adequacy
/// - hypothesis: L3 — zero at a positive scale reduces to scale zero; L2 —
///   random forms lifted by a random shift reduce back to themselves.
/// - witness: `tests::amplitudes::a_scaled_form_reduces_to_its_own`
/// - witness: `tests::amplitudes::zero_at_any_scale_is_zero`
#[spec(ensures: |ref ret| ret.scale <= scale && (ret.scale.0 == 0 || (ret.real.rational | ret.real.irrational | ret.imaginary.rational | ret.imaginary.irrational) & 1 != 0))]
fn reduced(
    real: Root2,
    imaginary: Root2,
    scale: Scale,
) -> Amplitude
{
    if real == Root2::ZERO && imaginary == Root2::ZERO {
        return Amplitude::ZERO;
    }
    let (mut real, mut imaginary, mut scale) = (real, imaginary, scale.0);
    while scale > 0
        && (real.rational | real.irrational | imaginary.rational | imaginary.irrational) & 1 == 0
    {
        real = real.halved();
        imaginary = imaginary.halved();
        scale = scale.saturating_sub(1);
    }
    Amplitude {
        real,
        imaginary,
        scale: Scale(scale),
    }
}

/// The real amplitude `value / 2^scale` at its least scale.
///
/// # Specification
/// - ensures: the same value at the least scale that keeps both coefficients
///   integers; zero at scale zero.
/// - panics: none.
/// - intension: at most 127 halvings.
///
/// # Adequacy
/// - hypothesis: L3 — the squared modulus of `1/√2` is one half at scale one.
/// - witness: `tests::amplitudes::the_squared_moduli_of_h_t_h_sum_to_one`
/// - witness: `tests::amplitudes::zero_at_any_scale_is_zero`
#[spec(ensures: |ref ret| ret.scale <= scale && (ret.scale.0 == 0 || (ret.value.rational | ret.value.irrational) & 1 != 0))]
fn reduced_real(
    value: Root2,
    scale: Scale,
) -> RealAmplitude
{
    if value == Root2::ZERO {
        return RealAmplitude::ZERO;
    }
    let (mut value, mut scale) = (value, scale.0);
    while scale > 0 && (value.rational | value.irrational) & 1 == 0 {
        value = value.halved();
        scale = scale.saturating_sub(1);
    }
    RealAmplitude {
        value,
        scale: Scale(scale),
    }
}

/// An element `(a + b√2 + (c + d√2)i) / 2^k` of `ℤ[1/√2, i]`, with integer
/// coefficients and the least `k`.
///
/// # Specification
/// - ensures: the scale is the least that keeps the four coefficients integers,
///   so equal amplitudes have equal forms.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is the constructors',
///   which reduce each form.
///
/// # Adequacy
/// - hypothesis: L3 — a form with every coefficient even at a positive scale
///   reduces; L2 — random forms lifted by a random shift reduce back to
///   themselves.
/// - witness: `tests::amplitudes::a_scaled_form_reduces_to_its_own`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Amplitude
{
    /// `a + b√2`.
    real: Root2,
    /// `c + d√2`.
    imaginary: Root2,
    /// `k`.
    scale: Scale,
}

impl Amplitude
{
    /// `i`, the square root of minus one.
    pub const I: Self = Self {
        real: Root2::ZERO,
        imaginary: Root2 {
            rational: 1,
            irrational: 0,
        },
        scale: Scale(0),
    };
    /// `ω = e^{iπ/4} = (√2 + √2 i)/2`, the phase of the `T` gate.
    pub const OMEGA: Self = Self {
        real: Root2 {
            rational: 0,
            irrational: 1,
        },
        imaginary: Root2 {
            rational: 0,
            irrational: 1,
        },
        scale: Scale(1),
    };
    /// `−1/√2 = −√2/2`, the lower right entry of the Hadamard gate.
    pub(crate) const MINUS_SQRT_HALF: Self = Self {
        real: Root2 {
            rational: 0,
            irrational: -1,
        },
        imaginary: Root2::ZERO,
        scale: Scale(1),
    };
    /// One.
    pub const ONE: Self = Self {
        real: Root2 {
            rational: 1,
            irrational: 0,
        },
        imaginary: Root2::ZERO,
        scale: Scale(0),
    };
    /// `1/√2 = √2/2`, the entry of the Hadamard gate.
    pub const SQRT_HALF: Self = Self {
        real: Root2 {
            rational: 0,
            irrational: 1,
        },
        imaginary: Root2::ZERO,
        scale: Scale(1),
    };
    /// Zero.
    pub const ZERO: Self = Self {
        real: Root2::ZERO,
        imaginary: Root2::ZERO,
        scale: Scale(0),
    };

    /// The amplitude `(rational + root · √2 + (imaginary + imaginary_root ·
    /// √2)i) / 2^scale`, at its least scale.
    ///
    /// # Specification
    /// - ensures: the amplitude of that value, reduced to its least scale.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — random forms lifted by a random shift reduce back to
    ///   themselves.
    /// - witness: `tests::amplitudes::a_scaled_form_reduces_to_its_own`
    #[spec(ensures: |ref ret| ret.scale <= scale && (ret.scale.0 == 0 || (ret.real.rational | ret.real.irrational | ret.imaginary.rational | ret.imaginary.irrational) & 1 != 0))]
    #[inline]
    #[must_use]
    pub fn new(
        rational: Coefficient,
        root: Coefficient,
        imaginary: Coefficient,
        imaginary_root: Coefficient,
        scale: Scale,
    ) -> Self
    {
        reduced(
            Root2 {
                rational: rational.0,
                irrational: root.0,
            },
            Root2 {
                rational: imaginary.0,
                irrational: imaginary_root.0,
            },
            scale,
        )
    }

    /// The coefficients `a`, `b`, `c` and `d` of `(a + b√2 + (c + d√2)i) /
    /// 2^k`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn coefficients(&self) -> [Coefficient; 4]
    {
        [
            Coefficient(self.real.rational),
            Coefficient(self.real.irrational),
            Coefficient(self.imaginary.rational),
            Coefficient(self.imaginary.irrational),
        ]
    }

    /// The scale `k` of `(a + b√2 + (c + d√2)i) / 2^k`, the least one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn scale(&self) -> Scale
    {
        self.scale
    }

    /// Both forms at the scale `scale`, which is at least each one's own.
    ///
    /// # Specification
    /// - requires: `scale` is at least the amplitude's scale.
    /// - ensures: the parts multiplied by `2` to the difference of the scales.
    /// - fails: a part past the 128-bit integers is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Outside`]: a lifted part lies past the 128-bit integers.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a sum of amplitudes at scales zero and two lifts the
    ///   first.
    /// - witness: `tests::amplitudes::the_state_of_h_t_h_on_zero_is_exact`
    #[spec(requires: scale >= self.scale)]
    fn lifted(
        &self,
        scale: Scale,
    ) -> Result<(Root2, Root2), Outside>
    {
        let shift = Scale(scale.0.saturating_sub(self.scale.0));
        Ok((self.real.scaled(shift)?, self.imaginary.scaled(shift)?))
    }

    /// The exact sum.
    ///
    /// # Specification
    /// - ensures: the sum at its least scale.
    /// - fails: a coefficient past the 128-bit integers is refused.
    /// - panics: none.
    /// - intension: the operand at the lower scale lifts to the higher one, and
    ///   zero returns the other operand without a lift.
    ///
    /// # Errors
    /// - [`Outside`]: a coefficient of the lifted operands or of the sum lies
    ///   past the 128-bit integers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the ring laws on generated amplitudes; L3 — the state
    ///   of `H T H` on `|0⟩` and a sum past the integers.
    /// - witness: `tests::amplitudes::the_amplitudes_pass_every_ring_law`
    /// - witness: `tests::amplitudes::the_state_of_h_t_h_on_zero_is_exact`
    /// - witness: `tests::amplitudes::a_coefficient_past_128_bits_is_refused`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |sum| (*self != Self::ZERO || sum == other)
        && (sum.scale.0 == 0 || (sum.real.rational | sum.real.irrational | sum.imaginary.rational | sum.imaginary.irrational) & 1 != 0)))]
    #[inline]
    pub fn add(
        &self,
        other: &Self,
    ) -> Result<Self, Outside>
    {
        if *self == Self::ZERO {
            return Ok(*other);
        }
        if *other == Self::ZERO {
            return Ok(*self);
        }
        let scale = self.scale.max(other.scale);
        let (left_real, left_imaginary) = self.lifted(scale)?;
        let (right_real, right_imaginary) = other.lifted(scale)?;
        Ok(reduced(
            left_real.add(right_real)?,
            left_imaginary.add(right_imaginary)?,
            scale,
        ))
    }

    /// The exact product: sixteen products of coefficients, the scales summed,
    /// then one reduction.
    ///
    /// # Specification
    /// - ensures: the product at its least scale.
    /// - fails: a coefficient, a partial product or a partial sum past the
    ///   128-bit integers is refused, and so is a scale past `u32::MAX`.
    /// - panics: none.
    /// - intension: a zero operand returns zero with no product.
    ///
    /// # Errors
    /// - [`Outside`]: a coefficient, a partial product or sum, or the scale
    ///   lies past what the form represents.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the ring laws on generated amplitudes and the gates'
    ///   unitarity; L3 — a product past the integers.
    /// - witness: `tests::amplitudes::the_amplitudes_pass_every_ring_law`
    /// - witness: `tests::gates::each_gate_is_unitary`
    /// - witness: `tests::amplitudes::a_coefficient_past_128_bits_is_refused`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |product| ((*self != Self::ZERO && *other != Self::ZERO) || *product == Self::ZERO)
        && (product.scale.0 == 0 || (product.real.rational | product.real.irrational | product.imaginary.rational | product.imaginary.irrational) & 1 != 0)))]
    #[inline]
    pub fn multiply(
        &self,
        other: &Self,
    ) -> Result<Self, Outside>
    {
        if *self == Self::ZERO || *other == Self::ZERO {
            return Ok(Self::ZERO);
        }
        let scale = Scale(self.scale.0.checked_add(other.scale.0).ok_or(Outside)?);
        let real = self
            .real
            .multiply(other.real)?
            .subtract(self.imaginary.multiply(other.imaginary)?)?;
        let imaginary = self
            .real
            .multiply(other.imaginary)?
            .add(self.imaginary.multiply(other.real)?)?;
        Ok(reduced(real, imaginary, scale))
    }

    /// The exact negation.
    ///
    /// # Specification
    /// - ensures: every coefficient negated at the same scale, which stays the
    ///   least.
    /// - fails: a coefficient that is the least 128-bit integer is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Outside`]: a coefficient is the least 128-bit integer.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the additive inverse law; L3 — the least integer.
    /// - witness: `tests::amplitudes::the_amplitudes_pass_every_ring_law`
    /// - witness: `tests::amplitudes::a_coefficient_past_128_bits_is_refused`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |negation| negation.scale == self.scale
        && negation.coefficients().iter().zip(self.coefficients()).all(|(negated, coefficient)| negated.0.wrapping_add(coefficient.0) == 0)))]
    #[inline]
    pub fn negate(&self) -> Result<Self, Outside>
    {
        Ok(Self {
            real: self.real.negate()?,
            imaginary: self.imaginary.negate()?,
            scale: self.scale,
        })
    }

    /// The exact complex conjugate, `(a + b√2 − (c + d√2)i) / 2^k`.
    ///
    /// # Specification
    /// - ensures: the imaginary coefficients negated at the same scale, which
    ///   stays the least.
    /// - fails: an imaginary coefficient that is the least 128-bit integer is
    ///   refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Outside`]: an imaginary coefficient is the least 128-bit integer.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — `U · U† = I` for each gate reads every conjugate.
    /// - witness: `tests::gates::each_gate_is_unitary`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |conjugate| conjugate.scale == self.scale && conjugate.real == self.real
        && conjugate.imaginary.rational.wrapping_add(self.imaginary.rational) == 0
        && conjugate.imaginary.irrational.wrapping_add(self.imaginary.irrational) == 0))]
    #[inline]
    pub fn conjugate(&self) -> Result<Self, Outside>
    {
        Ok(Self {
            real: self.real,
            imaginary: self.imaginary.negate()?,
            scale: self.scale,
        })
    }

    /// The squared modulus `|z|² = z · z̄`, which lies in `ℤ[1/√2]`.
    ///
    /// # Specification
    /// - ensures: `((a + b√2)² + (c + d√2)²) / 4^k` at its least scale.
    /// - fails: a coefficient past the 128-bit integers, or a scale past
    ///   `u32::MAX`, is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Outside`]: a coefficient or the scale of the square lies past what
    ///   the form represents.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the state of `H T H` on `|0⟩` has the squared moduli
    ///   `(2 + √2)/4` and `(2 − √2)/4`, which sum to one.
    /// - witness: `tests::amplitudes::the_squared_moduli_of_h_t_h_sum_to_one`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |square| (*self != Self::ZERO || *square == RealAmplitude::ZERO)
        && (square.scale.0 == 0 || (square.value.rational | square.value.irrational) & 1 != 0)))]
    #[inline]
    pub fn squared_modulus(&self) -> Result<RealAmplitude, Outside>
    {
        let scale = Scale(self.scale.0.checked_mul(2).ok_or(Outside)?);
        let value = self.real.squared()?.add(self.imaginary.squared()?)?;
        Ok(reduced_real(value, scale))
    }
}

impl From<RealAmplitude> for Amplitude
{
    /// The real amplitude as an amplitude with no imaginary part.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(real: RealAmplitude) -> Self
    {
        Self {
            real: real.value,
            imaginary: Root2::ZERO,
            scale: real.scale,
        }
    }
}

/// An element `(a + b√2) / 2^k` of the real subring `ℤ[1/√2]`, with integer
/// coefficients and the least `k`.
///
/// # Specification
/// - ensures: the scale is the least that keeps both coefficients integers, so
///   equal values have equal forms.
/// - panics: none.
/// - executable: none — a type-level block: the invariant is the constructors',
///   which reduce each form.
///
/// # Adequacy
/// - hypothesis: L3 — the squared moduli of the state of `H T H` on `|0⟩` and
///   their sum, one.
/// - witness: `tests::amplitudes::the_squared_moduli_of_h_t_h_sum_to_one`
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct RealAmplitude
{
    /// `a + b√2`.
    value: Root2,
    /// `k`.
    scale: Scale,
}

impl RealAmplitude
{
    /// One.
    pub const ONE: Self = Self {
        value: Root2 {
            rational: 1,
            irrational: 0,
        },
        scale: Scale(0),
    };
    /// Zero.
    pub const ZERO: Self = Self {
        value: Root2::ZERO,
        scale: Scale(0),
    };

    /// The real amplitude `(rational + root · √2) / 2^scale`, at its least
    /// scale.
    ///
    /// # Specification
    /// - ensures: the real amplitude of that value, reduced to its least scale.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the squared moduli of the state of `H T H` on `|0⟩`.
    /// - witness: `tests::amplitudes::the_squared_moduli_of_h_t_h_sum_to_one`
    #[spec(ensures: |ref ret| ret.scale <= scale && (ret.scale.0 == 0 || (ret.value.rational | ret.value.irrational) & 1 != 0))]
    #[inline]
    #[must_use]
    pub fn new(
        rational: Coefficient,
        root: Coefficient,
        scale: Scale,
    ) -> Self
    {
        reduced_real(
            Root2 {
                rational: rational.0,
                irrational: root.0,
            },
            scale,
        )
    }

    /// The coefficients `a` and `b` of `(a + b√2) / 2^k`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn coefficients(&self) -> [Coefficient; 2]
    {
        [
            Coefficient(self.value.rational),
            Coefficient(self.value.irrational),
        ]
    }

    /// The scale `k` of `(a + b√2) / 2^k`, the least one.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn scale(&self) -> Scale
    {
        self.scale
    }

    /// The exact sum.
    ///
    /// # Specification
    /// - ensures: the sum at its least scale.
    /// - fails: a coefficient past the 128-bit integers is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Outside`]: a coefficient of the lifted operands or of the sum lies
    ///   past the 128-bit integers.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the ring laws on generated real amplitudes; L3 — the
    ///   squared moduli of `H T H` on `|0⟩` sum to one.
    /// - witness: `tests::amplitudes::the_real_amplitudes_pass_every_ring_law`
    /// - witness: `tests::amplitudes::the_squared_moduli_of_h_t_h_sum_to_one`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |sum| (*self != Self::ZERO || sum == other)
        && (sum.scale.0 == 0 || (sum.value.rational | sum.value.irrational) & 1 != 0)))]
    #[inline]
    pub fn add(
        &self,
        other: &Self,
    ) -> Result<Self, Outside>
    {
        let scale = self.scale.max(other.scale);
        let left = self
            .value
            .scaled(Scale(scale.0.saturating_sub(self.scale.0)))?;
        let right = other
            .value
            .scaled(Scale(scale.0.saturating_sub(other.scale.0)))?;
        Ok(reduced_real(left.add(right)?, scale))
    }

    /// The exact product.
    ///
    /// # Specification
    /// - ensures: the product at its least scale.
    /// - fails: a coefficient, a partial product or sum, or a scale past
    ///   `u32::MAX` is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Outside`]: a coefficient, a partial product or sum, or the scale
    ///   lies past what the form represents.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the ring laws on generated real amplitudes.
    /// - witness: `tests::amplitudes::the_real_amplitudes_pass_every_ring_law`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |product| ((*self != Self::ZERO && *other != Self::ZERO) || *product == Self::ZERO)
        && (product.scale.0 == 0 || (product.value.rational | product.value.irrational) & 1 != 0)))]
    #[inline]
    pub fn multiply(
        &self,
        other: &Self,
    ) -> Result<Self, Outside>
    {
        let scale = Scale(self.scale.0.checked_add(other.scale.0).ok_or(Outside)?);
        Ok(reduced_real(self.value.multiply(other.value)?, scale))
    }

    /// The exact negation.
    ///
    /// # Specification
    /// - ensures: both coefficients negated at the same scale, which stays the
    ///   least.
    /// - fails: a coefficient that is the least 128-bit integer is refused.
    /// - panics: none.
    ///
    /// # Errors
    /// - [`Outside`]: a coefficient is the least 128-bit integer.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the additive inverse law on generated real
    ///   amplitudes.
    /// - witness: `tests::amplitudes::the_real_amplitudes_pass_every_ring_law`
    #[spec(ensures: |ref ret| ret.as_ref().map_or(true, |negation| negation.scale == self.scale
        && negation.value.rational.wrapping_add(self.value.rational) == 0
        && negation.value.irrational.wrapping_add(self.value.irrational) == 0))]
    #[inline]
    pub fn negate(&self) -> Result<Self, Outside>
    {
        Ok(Self {
            value: self.value.negate()?,
            scale: self.scale,
        })
    }
}

/// The commutative ring `ℤ[1/√2, i]` under the discrete order, on the
/// elements a check generates.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Amplitudes
{
    /// The elements a check reads.
    generated: Vec<Amplitude>,
}

impl Amplitudes
{
    /// The ring whose check reads `generated`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn generated(generated: Vec<Amplitude>) -> Self
    {
        Self { generated }
    }
}

impl OrderedSemiring for Amplitudes
{
    type Element = Amplitude;

    /// `amplitudes`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn name(&self) -> InstanceName
    {
        InstanceName::from("amplitudes")
    }

    /// The generated elements.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn carrier(&self) -> Carrier<'_, Amplitude>
    {
        Carrier::Generated(&self.generated)
    }

    /// Zero.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn zero(&self) -> Amplitude
    {
        Amplitude::ZERO
    }

    /// One.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn one(&self) -> Amplitude
    {
        Amplitude::ONE
    }

    /// The exact sum.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn add(
        &self,
        left: &Amplitude,
        right: &Amplitude,
    ) -> Result<Amplitude, Outside>
    {
        left.add(right)
    }

    /// The exact product.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn multiply(
        &self,
        left: &Amplitude,
        right: &Amplitude,
    ) -> Result<Amplitude, Outside>
    {
        left.multiply(right)
    }

    /// The discrete order: an amplitude lies below itself alone.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn compare(
        &self,
        lower: &Amplitude,
        upper: &Amplitude,
    ) -> Comparison
    {
        if lower == upper {
            Comparison::Below
        }
        else {
            Comparison::NotBelow
        }
    }
}

impl CommutativeRing for Amplitudes
{
    /// The exact negation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn negate(
        &self,
        element: &Amplitude,
    ) -> Result<Amplitude, Outside>
    {
        element.negate()
    }
}

/// The commutative ring `ℤ[1/√2]` under the discrete order, on the elements a
/// check generates.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct RealAmplitudes
{
    /// The elements a check reads.
    generated: Vec<RealAmplitude>,
}

impl RealAmplitudes
{
    /// The ring whose check reads `generated`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn generated(generated: Vec<RealAmplitude>) -> Self
    {
        Self { generated }
    }
}

impl OrderedSemiring for RealAmplitudes
{
    type Element = RealAmplitude;

    /// `real-amplitudes`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn name(&self) -> InstanceName
    {
        InstanceName::from("real-amplitudes")
    }

    /// The generated elements.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn carrier(&self) -> Carrier<'_, RealAmplitude>
    {
        Carrier::Generated(&self.generated)
    }

    /// Zero.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn zero(&self) -> RealAmplitude
    {
        RealAmplitude::ZERO
    }

    /// One.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn one(&self) -> RealAmplitude
    {
        RealAmplitude::ONE
    }

    /// The exact sum.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn add(
        &self,
        left: &RealAmplitude,
        right: &RealAmplitude,
    ) -> Result<RealAmplitude, Outside>
    {
        left.add(right)
    }

    /// The exact product.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn multiply(
        &self,
        left: &RealAmplitude,
        right: &RealAmplitude,
    ) -> Result<RealAmplitude, Outside>
    {
        left.multiply(right)
    }

    /// The discrete order: a real amplitude lies below itself alone.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn compare(
        &self,
        lower: &RealAmplitude,
        upper: &RealAmplitude,
    ) -> Comparison
    {
        if lower == upper {
            Comparison::Below
        }
        else {
            Comparison::NotBelow
        }
    }
}

impl CommutativeRing for RealAmplitudes
{
    /// The exact negation.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn negate(
        &self,
        element: &RealAmplitude,
    ) -> Result<RealAmplitude, Outside>
    {
        element.negate()
    }
}
