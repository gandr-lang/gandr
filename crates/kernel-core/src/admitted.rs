//! The admission policy: whether the kernel takes a tier's answer for a
//! conversion pair, and how many answers one check took.
//!
//! An admitted result is a reflexivity side whose dialogue is the one
//! decision `Admitted`: a tier outside the kernel ran the point and the
//! endpoint, both closed, to one normal form. Under
//! [`AdmissionPolicy::Derive`], the default, the kernel converts such a pair
//! by its own evaluation, as it does a side whose dialogue is `Evaluate`, and
//! refuses a pair that does not convert. Under
//! [`AdmissionPolicy::NativeConversion`] it takes a closed pair's answer
//! without deriving it, and the tier is in the trusted base for that run. An
//! open pair is derived under either policy.
//!
//! A check counts the answers it took. The
//! [`Environment`](crate::Environment) records no verdict for a declaration
//! whose check took one, since a receipt attests only what the kernel checked
//! itself, and it sums the run's answers for its report.

use core::cell::Cell;

use anodized::spec;
use gandr_kernel_term::TermArena;
use gandr_kernel_term::ValueId;

/// Whether the kernel takes an admitted result without deriving it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, PartialEq)]
pub enum AdmissionPolicy
{
    /// The kernel derives every admitted result by its own evaluation.
    #[default]
    Derive,
    /// The kernel takes a closed pair's admitted result from the native
    /// conversion tier that answered it.
    NativeConversion,
}

/// How many admitted results the kernel took.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct AdmittedCount(u32);

impl AdmittedCount
{
    /// No admitted result taken.
    pub const NONE: Self = Self(0);

    /// This count and `other` together, saturating.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn and(
        self,
        other: Self,
    ) -> Self
    {
        Self(self.0.saturating_add(other.0))
    }
}

impl From<AdmittedCount> for u32
{
    /// The count as a number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: AdmittedCount) -> Self
    {
        count.0
    }
}

/// Where one check stands on admitted results: deriving each, or taking each
/// closed pair's and counting it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Taking<'check>
{
    /// Derive every admitted result.
    Deriving,
    /// Take each closed pair's admitted result, counting it here.
    Counting(&'check Cell<AdmittedCount>),
}

/// What [`Taking::take`] did with a pair.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Took
{
    /// The kernel took the answer and counted it.
    Taken,
    /// The kernel derives the pair by its own evaluation.
    Derived,
}

impl<'check> Taking<'check>
{
    /// The stance `policy` gives a check, counting what it takes into
    /// `taken`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) const fn under(
        policy: AdmissionPolicy,
        taken: &'check Cell<AdmittedCount>,
    ) -> Self
    {
        match policy {
            AdmissionPolicy::Derive => Self::Deriving,
            AdmissionPolicy::NativeConversion => Self::Counting(taken),
        }
    }

    /// How many admitted results this stance has taken.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    pub(crate) fn taken(self) -> AdmittedCount
    {
        match self {
            Self::Deriving => AdmittedCount::NONE,
            Self::Counting(taken) => taken.get(),
        }
    }

    /// Take the admitted result relating `point` and `endpoint`, or leave the
    /// pair to the kernel's own evaluation.
    ///
    /// # Specification
    /// - requires: both values live in `arena`.
    /// - ensures: [`Took::Taken`] exactly when the stance counts and both
    ///   values are closed, the count then one higher; [`Took::Derived`]
    ///   otherwise, the count unchanged.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — under the policy a closed pair is taken and counted
    ///   and an open one is derived; without it nothing is taken.
    /// - witness: `element_identity::tests::an_admitted_result_is_taken_only_under_the_policy_3558`
    #[spec(
        captures: before = self.taken(),
        ensures: |ret| {
            let closed = u32::from(arena.value_support(point).depth()) == 0
                && u32::from(arena.value_support(endpoint).depth()) == 0;
            (ret == Took::Taken) == (matches!(self, Self::Counting(_)) && closed)
                && self.taken() == if ret == Took::Taken { before.and(AdmittedCount(1)) } else { before }
        },
    )]
    pub(crate) fn take(
        self,
        arena: &TermArena,
        point: ValueId,
        endpoint: ValueId,
    ) -> Took
    {
        let Self::Counting(taken) = self
        else {
            return Took::Derived;
        };
        let closed = [point, endpoint]
            .into_iter()
            .all(|side| u32::from(arena.value_support(side).depth()) == 0);
        if !closed {
            return Took::Derived;
        }
        taken.set(taken.get().and(AdmittedCount(1)));
        Took::Taken
    }
}
