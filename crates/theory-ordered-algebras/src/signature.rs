//! The signature of an ordered semiring, and the elements a check reads.

use core::fmt;
use core::fmt::Debug;

/// The name of an instance, which each refusal carries.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct InstanceName(&'static str);

impl From<&'static str> for InstanceName
{
    /// The instance named `name`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(name: &'static str) -> Self
    {
        Self(name)
    }
}

impl fmt::Display for InstanceName
{
    /// Writes the name.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(self.0)
    }
}

/// Whether one element lies below another in an instance's order.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Comparison
{
    /// The first lies below the second, or equals it.
    Below,
    /// The first does not lie below the second.
    NotBelow,
}

/// An operation whose exact result lies past the elements the instance
/// represents.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Outside;

/// The elements a check reads.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Carrier<'elements, E>
{
    /// Every element of a finite carrier, so a check decides each law.
    Whole(&'elements [E]),
    /// Elements an instance generates from an infinite carrier, so a check
    /// decides each law on these elements only.
    Generated(&'elements [E]),
}

impl<E> Carrier<'_, E>
{
    /// The elements, whichever kind of carrier holds them.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn elements(&self) -> &[E]
    {
        match *self {
            Self::Whole(elements) | Self::Generated(elements) => elements,
        }
    }
}

/// An ordered semiring: a carrier with an order, a zero, a one, an addition
/// and a multiplication. The laws are the checker's to decide, so a value of
/// this trait states the operations only.
///
/// # Specification
/// - provides: the operations [`crate::check`] decides the laws of.
/// - panics: none of its own.
/// - executable: none — the trait states obligations its implementations carry.
pub trait OrderedSemiring
{
    /// One element of the carrier.
    type Element: Clone + Debug + Eq;

    /// The instance's name, which each refusal carries.
    ///
    /// # Specification
    /// trivial.
    fn name(&self) -> InstanceName;

    /// The elements a check reads: the whole carrier when it is finite, and
    /// generated elements when it is not.
    ///
    /// # Specification
    /// trivial.
    fn carrier(&self) -> Carrier<'_, Self::Element>;

    /// The unit of addition.
    ///
    /// # Specification
    /// trivial.
    fn zero(&self) -> Self::Element;

    /// The unit of multiplication.
    ///
    /// # Specification
    /// trivial.
    fn one(&self) -> Self::Element;

    /// The sum of two elements.
    ///
    /// # Specification
    /// - ensures: the exact sum, or a refusal when it lies past the represented
    ///   elements.
    /// - panics: none.
    /// - executable: none — the sum is the implementation's.
    ///
    /// # Errors
    /// - [`Outside`]: the exact sum lies past the represented elements.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the law checker reads each implementation's sum on
    ///   every tuple of its carrier.
    /// - declaration-only: the obligation is each implementation's sum; the
    ///   trait has no body to witness.
    fn add(
        &self,
        left: &Self::Element,
        right: &Self::Element,
    ) -> Result<Self::Element, Outside>;

    /// The product of two elements.
    ///
    /// # Specification
    /// - ensures: the exact product, or a refusal when it lies past the
    ///   represented elements.
    /// - panics: none.
    /// - executable: none — the product is the implementation's.
    ///
    /// # Errors
    /// - [`Outside`]: the exact product lies past the represented elements.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the law checker reads each implementation's product
    ///   on every tuple of its carrier.
    /// - declaration-only: the obligation is each implementation's product; the
    ///   trait has no body to witness.
    fn multiply(
        &self,
        left: &Self::Element,
        right: &Self::Element,
    ) -> Result<Self::Element, Outside>;

    /// Whether `lower` lies below `upper` in the instance's order.
    ///
    /// # Specification
    /// trivial.
    fn compare(
        &self,
        lower: &Self::Element,
        upper: &Self::Element,
    ) -> Comparison;
}

/// A commutative ring under the discrete order.
///
/// It is an ordered semiring whose every element has a negation. The checker
/// decides the commutativity of the product and the inverse of the sum beside
/// the sixteen laws.
///
/// # Specification
/// - provides: the negation [`crate::check_ring`] decides the inverse law on.
/// - panics: none of its own.
/// - executable: none — the trait states obligations its implementations carry.
pub trait CommutativeRing: OrderedSemiring
{
    /// The negation of an element: the element whose sum with it is zero.
    ///
    /// # Specification
    /// - ensures: the exact negation, or a refusal when it lies past the
    ///   represented elements.
    /// - panics: none.
    /// - executable: none — the negation is the implementation's.
    ///
    /// # Errors
    /// - [`Outside`]: the exact negation lies past the represented elements.
    ///
    /// # Adequacy
    /// - hypothesis: L2 — the ring checker reads each implementation's negation
    ///   on every element of its carrier.
    /// - declaration-only: the obligation is each implementation's negation;
    ///   the trait has no body to witness.
    fn negate(
        &self,
        element: &Self::Element,
    ) -> Result<Self::Element, Outside>;
}
