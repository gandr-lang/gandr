//! The jump budget of a run: the count of code-word jumps it may take, where
//! that count comes from, and the report a run gives when it spends it.
//!
//! The budget is a policy of the invocation. The driver binds it once with
//! [`bind`], from `--run-budget`, before the first run. Without a binding, a
//! run has no budget ([`Budget::NONE`]). It counts its jumps down from the
//! widest count, so the jump path keeps its one decrement and its one compare.
//! Each run that the dispatcher starts reads the one budget of its process
//! with [`bound`]. A caller that runs a command of its own, as a test or a
//! probe does, names its own budget with [`Budget::from`].
//!
//! A budget counts jumps and not time, so a stop replays the same on every
//! host.
//!
//! # References
//!
//! - `vault:01a178aa-608d-75d0-8f71-e6fe4289f327` — lineage: the compiled
//!   runtime's representation question (§ runtime-question-what-runtime-means):
//!   the compiled code reads its fuel from the record that its caller gives.

use core::fmt;
use core::num::NonZeroU64;
use core::str::FromStr;
use std::sync::OnceLock;

use gandr_runtime_stencils::Fuel;

use crate::regions::Grouped;

/// The invocation's budget, bound once.
static BOUND: OnceLock<Budget> = OnceLock::new();

/// A count of code-word jumps: one jump at least.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Jumps(NonZeroU64);

impl TryFrom<u64> for Jumps
{
    type Error = Uncounted;

    /// This many jumps.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Uncounted::Zero`] for zero, which runs no code word.
    #[inline]
    fn try_from(jumps: u64) -> Result<Self, Uncounted>
    {
        NonZeroU64::new(jumps).map(Self).ok_or(Uncounted::Zero)
    }
}

/// Why a text names no count of jumps.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Uncounted
{
    /// The text is empty, or holds a character that is not a decimal digit.
    Digits,
    /// The count passes the widest count of jumps.
    Overflow,
    /// The count is zero, which runs no code word.
    Zero,
}

impl fmt::Display for Uncounted
{
    /// Why the text names no count, in a line.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(match *self {
            Self::Digits => "a budget is a count of jumps in decimal digits, as `16777216` is",
            Self::Overflow => "the count passes the widest count of jumps",
            Self::Zero => "a budget of zero jumps runs no code word",
        })
    }
}

impl core::error::Error for Uncounted
{
}

impl FromStr for Jumps
{
    type Err = Uncounted;

    /// The count that `text` writes in decimal digits, with no sign and no
    /// unit.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Errors
    /// [`Uncounted`] naming why `text` names no count.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a count reads, and an empty text, a sign, a unit, an
    ///   overflow and zero each refuse with their own reason.
    /// - witness: `budget::tests::a_count_reads_its_digits_and_refuses_the_rest`
    #[inline]
    fn from_str(text: &str) -> Result<Self, Uncounted>
    {
        if text.is_empty() || !text.bytes().all(|byte| byte.is_ascii_digit()) {
            return Err(Uncounted::Digits);
        }
        let count: u64 = text.parse().map_err(|_overflow| Uncounted::Overflow)?;
        Self::try_from(count)
    }
}

/// Where a run's budget comes from.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Origin
{
    /// The invocation's `--run-budget`.
    Flag,
    /// The budget of a server whose invocation names none.
    Served,
    /// The budget that the caller of the run names, as a test or a probe
    /// does.
    Caller,
    /// No budget: the widest count.
    None,
}

/// The jump budget of a run, and its origin.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Budget
{
    /// The jumps that the run may take.
    jumps: u64,
    /// Where they come from.
    origin: Origin,
}

impl Budget
{
    /// No budget: the run counts down from the widest count, and it stops only
    /// when it halts or when a region stops it at the memory bound.
    pub const NONE: Self = Self {
        jumps: u64::MAX,
        origin: Origin::None,
    };

    /// The budget of a server whose invocation names none: 2²⁴ jumps. A
    /// session judges each run claim before it answers, and a newer revision
    /// does not stop a run. Thus a server bounds each run that its invocation
    /// leaves without a budget.
    pub const SERVED: Self = Self {
        jumps: 1_u64 << 24_u32,
        origin: Origin::Served,
    };

    /// The budget that the invocation's `--run-budget` names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn flag(jumps: Jumps) -> Self
    {
        Self {
            jumps: jumps.0.get(),
            origin: Origin::Flag,
        }
    }

    /// Where the budget comes from.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn origin(self) -> Origin
    {
        self.origin
    }

    /// The fuel that a run's record starts with.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub(crate) fn fuel(self) -> Fuel
    {
        Fuel::from(usize::try_from(self.jumps).unwrap_or(usize::MAX))
    }

    /// The budget of a run that the run of this budget starts with `fuel`
    /// left: the same origin, over the jumps left.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    pub(crate) fn left(
        self,
        fuel: Fuel,
    ) -> Self
    {
        Self {
            jumps: u64::try_from(usize::from(fuel)).unwrap_or(u64::MAX),
            origin: self.origin,
        }
    }

    /// The stop of a run that spent this budget, as the report states it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub const fn spent(self) -> Spent
    {
        Spent(self)
    }
}

impl From<usize> for Budget
{
    /// The budget of `jumps` that the caller of a run names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(jumps: usize) -> Self
    {
        Self {
            jumps: u64::try_from(jumps).unwrap_or(u64::MAX),
            origin: Origin::Caller,
        }
    }
}

impl fmt::Display for Budget
{
    /// The budget with its origin: `--run-budget 16777216`, or the origin
    /// with its count of jumps.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let jumps = Grouped::from(self.jumps);
        match self.origin {
            Origin::Flag => write!(f, "--run-budget {}", self.jumps),
            Origin::Served => write!(
                f,
                "the server's budget for an invocation that names none, {jumps} jumps"
            ),
            Origin::Caller => write!(f, "the caller's budget, {jumps} jumps"),
            Origin::None => write!(f, "no budget, the widest count of {jumps} jumps"),
        }
    }
}

/// The stop of a run that spent its budget.
///
/// # Specification
/// trivial.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Spent(Budget);

impl fmt::Display for Spent
{
    /// The stop as the report states it: the jumps spent, the budget with its
    /// origin, and the remedy.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a stop names the jumps, the origin and the remedy of
    ///   each origin, and two origins render apart.
    /// - witness: `budget::tests::a_stop_names_its_budget_its_origin_and_its_remedy`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let budget = self.0;
        write!(
            f,
            "the run spent its budget of {} jumps; the budget is {budget}; ",
            Grouped::from(budget.jumps)
        )?;
        f.write_str(match budget.origin {
            Origin::Flag => "raise --run-budget",
            Origin::Served => "start the server with a larger --run-budget",
            Origin::Caller => "raise it where its caller names it",
            Origin::None => "the run takes no larger count",
        })
    }
}

impl From<Budget> for u64
{
    /// The jumps that the run may take.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(budget: Budget) -> Self
    {
        budget.jumps
    }
}

/// Bind the invocation's budget, once, before its first run.
///
/// # Specification
/// - ensures: every later [`bound`] reads `budget`.
/// - executable: none — the binding is the process's.
///
/// # Adequacy
/// - hypothesis: L3 — a first binding and a later one: the first holds for
///   every read, and the later one is refused with the budget in force.
/// - witness: `budget::tests::the_first_binding_holds_and_a_later_one_is_refused`
///
/// # Errors
/// The budget already in force, when an earlier binding or a run fixed it.
#[inline]
pub fn bind(budget: Budget) -> Result<(), Budget>
{
    BOUND.set(budget).map_err(|_bound| bound())
}

/// The budget that each run the dispatcher starts takes: the budget that
/// [`bind`] gave, else no budget.
///
/// # Specification
/// trivial.
#[inline]
#[must_use]
pub fn bound() -> Budget
{
    *BOUND.get_or_init(|| Budget::NONE)
}

#[cfg(test)]
mod tests
{
    use alloc::string::ToString as _;

    use super::Budget;
    use super::Jumps;
    use super::Uncounted;
    use super::bind;
    use super::bound;

    /// A count of jumps reads its decimal digits, and refuses an empty text, a
    /// sign, a unit, an overflow and zero.
    #[test]
    fn a_count_reads_its_digits_and_refuses_the_rest()
    {
        assert_eq!(
            Jumps::try_from(1_u64 << 24_u32).ok(),
            "16777216".parse().ok(),
            "digits"
        );
        assert_eq!(Err(Uncounted::Digits), "".parse::<Jumps>(), "nothing");
        assert_eq!(Err(Uncounted::Digits), "+5".parse::<Jumps>(), "a sign");
        assert_eq!(Err(Uncounted::Digits), "16M".parse::<Jumps>(), "a unit");
        assert_eq!(
            Err(Uncounted::Overflow),
            "18446744073709551616".parse::<Jumps>(),
            "past the widest count"
        );
        assert_eq!(Err(Uncounted::Zero), "0".parse::<Jumps>(), "zero");
    }

    /// A stop names the jumps, the budget with its origin, and the remedy of
    /// that origin.
    #[test]
    fn a_stop_names_its_budget_its_origin_and_its_remedy()
    {
        let jumps = Jumps::try_from(1_u64 << 24_u32).expect("a count above zero");
        assert_eq!(
            "the run spent its budget of 16 777 216 jumps; the budget is --run-budget 16777216; \
             raise --run-budget",
            Budget::flag(jumps).spent().to_string()
        );
        assert_eq!(
            "the run spent its budget of 16 777 216 jumps; the budget is the server's budget for \
             an invocation that names none, 16 777 216 jumps; start the server with a larger \
             --run-budget",
            Budget::SERVED.spent().to_string()
        );
        assert_eq!(
            "the run spent its budget of 1 048 576 jumps; the budget is the caller's budget, 1 \
             048 576 jumps; raise it where its caller names it",
            Budget::from(1_usize << 20_u32).spent().to_string()
        );
    }

    /// The first binding holds for every read, and a later binding is
    /// refused with the budget in force. A test that read the budget first
    /// fixes it, so the first binding here may meet that budget.
    #[test]
    fn the_first_binding_holds_and_a_later_one_is_refused()
    {
        let first = Budget::flag(Jumps::try_from(1_000_u64).expect("a count above zero"));
        let held = bind(first).err().unwrap_or(first);
        assert_eq!(held, bound());
        assert_eq!(Err(held), bind(Budget::SERVED));
        assert_eq!(held, bound());
    }
}
