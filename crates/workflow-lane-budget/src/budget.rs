//! The budget table: a job's name and the seconds its median may take.

use core::fmt;
use core::num::NonZeroUsize;
use core::num::ParseIntError;
use core::str::FromStr;

use anodized::spec;

use crate::cone::Cone;
use crate::error::BudgetError;

/// Seconds in a minute, for the report's `9m 41s`.
const MINUTE: u64 = 60;

/// A job's display name, as the CI workflow names it.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Lane(String);

impl From<&str> for Lane
{
    /// Names the job `name`.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(name: &str) -> Self
    {
        Self(name.to_owned())
    }
}

impl fmt::Display for Lane
{
    /// Writes the job's name as the workflow spells it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// Whole seconds of job time.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct Seconds(u64);

impl From<u64> for Seconds
{
    /// The time `seconds` whole seconds take.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(seconds: u64) -> Self
    {
        Self(seconds)
    }
}

impl FromStr for Seconds
{
    type Err = ParseIntError;

    /// Reads whole seconds written in decimal.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from_str(text: &str) -> Result<Self, Self::Err>
    {
        text.parse().map(Self)
    }
}

impl fmt::Display for Seconds
{
    /// Writes the time as minutes and seconds: `9m 41s`, `0m 7s`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the whole minutes, `m `, the remaining seconds and
    ///   `s`.
    /// - provides: the report's time column.
    /// - fails: propagates the formatter's own write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — times under, at and past a minute; swapping the
    ///   quotient and the remainder or dropping the remainder changes the text.
    /// - witness: `budget::tests::a_time_reads_as_minutes_and_seconds`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let minutes = self.0.checked_div(MINUTE).unwrap_or_default();
        let seconds = self.0.checked_rem(MINUTE).unwrap_or_default();
        write!(f, "{minutes}m {seconds}s")
    }
}

/// One row of the budget table: a job, the cone it bounds, and the seconds
/// its median may take.
///
/// # Specification
/// - provides: what the report compares a lane's median against.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Budget
{
    /// The job, by its display name.
    pub lane: Lane,
    /// The cone this budget bounds; a lane without a deep budget is not
    /// cone-classified and its single row is held to this budget.
    pub cone: Cone,
    /// The most its median may take.
    pub limit: Seconds,
}

impl FromStr for Budget
{
    type Err = BudgetError;

    /// Reads `NAME=SECONDS` or `NAME:CONE=SECONDS`: the job's display name,
    /// an optional `:deep` or `:surface` cone, `=`, and whole seconds. A
    /// bare name is the surface budget; `:deep` names the deep budget of a
    /// cone-classified lane.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the name is the text before the last `=`, minus
    ///   any `:deep` or `:surface` cone, trimmed and not empty, the cone the
    ///   suffix names (surface without one), and the limit the decimal after
    ///   the `=`.
    /// - provides: the budget table's rows from the workflow's arguments.
    /// - fails: [`BudgetError::Budget`] when no `=` is present, the name is
    ///   empty, the cone is not `deep` or `surface`, or the seconds are not a
    ///   whole number.
    /// - panics: none.
    /// - executable: none — the outcome is the parse itself.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a name with parentheses and spaces, a name holding
    ///   `=`, a `:deep` and a `:surface` suffix, an unknown cone, an empty
    ///   name, a fraction and a missing `=`; splitting at the first `=`,
    ///   reading the cone before the name, or accepting an empty name changes a
    ///   parse.
    /// - witness: `budget::tests::a_budget_reads_name_cone_and_seconds`
    #[inline]
    fn from_str(text: &str) -> Result<Self, Self::Err>
    {
        let refuse = || BudgetError::Budget {
            text: text.to_owned(),
        };
        let (name, seconds) = text.rsplit_once('=').ok_or_else(refuse)?;
        let (name, cone) = if let Some(lane) = name.strip_suffix(":deep") {
            (lane, Cone::Deep)
        }
        else if let Some(lane) = name.strip_suffix(":surface") {
            (lane, Cone::Surface)
        }
        else if name.contains(':') {
            return Err(refuse());
        }
        else {
            (name, Cone::Surface)
        };
        let name = name.trim();
        if name.is_empty() {
            return Err(refuse());
        }
        let limit = seconds.trim().parse::<Seconds>().ok().ok_or_else(refuse)?;
        Ok(Self {
            lane: Lane::from(name),
            cone,
            limit,
        })
    }
}

/// How many of the latest runs a report reads; never zero.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RunCount(NonZeroUsize);

impl FromStr for RunCount
{
    type Err = ParseIntError;

    /// Reads a positive decimal count.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from_str(text: &str) -> Result<Self, Self::Err>
    {
        text.parse().map(Self)
    }
}

impl From<RunCount> for usize
{
    /// The count as a length.
    ///
    /// # Specification
    /// trivial.
    #[spec(ensures: |ret| ret == count.0.get())]
    #[inline]
    fn from(count: RunCount) -> Self
    {
        count.0.get()
    }
}

#[cfg(test)]
mod tests
{
    use super::Budget;
    use super::Lane;
    use super::Seconds;
    use crate::cone::Cone;
    use crate::error::BudgetError;

    #[test]
    fn a_budget_reads_name_cone_and_seconds()
    {
        assert_eq!(
            "test enforcing targets (linux)=600".parse::<Budget>(),
            Ok(Budget {
                lane: Lane::from("test enforcing targets (linux)"),
                cone: Cone::Surface,
                limit: Seconds::from(600),
            })
        );
        assert_eq!(
            "test enforcing targets (linux):deep=540".parse::<Budget>(),
            Ok(Budget {
                lane: Lane::from("test enforcing targets (linux)"),
                cone: Cone::Deep,
                limit: Seconds::from(540),
            })
        );
        assert_eq!(
            "a=b = 7".parse::<Budget>(),
            Ok(Budget {
                lane: Lane::from("a=b"),
                cone: Cone::Surface,
                limit: Seconds::from(7),
            })
        );
        for text in [
            "=600",
            "check Clippy wall",
            "check Clippy wall=1.5",
            "check Clippy wall:wide=600",
        ] {
            assert_eq!(
                text.parse::<Budget>(),
                Err(BudgetError::Budget { text: text.into() }),
                "{text}"
            );
        }
    }

    #[test]
    fn a_time_reads_as_minutes_and_seconds()
    {
        for (seconds, text) in [(7, "0m 7s"), (60, "1m 0s"), (581, "9m 41s")] {
            assert_eq!(Seconds::from(seconds).to_string(), text);
        }
    }
}
