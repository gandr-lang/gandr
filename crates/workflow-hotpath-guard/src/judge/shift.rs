//! The runner shift: how far every function of a run's full timing report
//! moved against its base's, and each function judged beside that move.
//!
//! A slower runner slows every function by about the same ratio, so the
//! **global shift** is the median ratio over every function both reports
//! time. A function regresses when its own ratio, divided by the shift, still
//! crosses the policy's threshold; a failed timing check in which none does,
//! while the wall time and the shift both do, is the runner's.
//!
//! The shift is read from the reports the series kept, never from the
//! check's summary: the summary lists only the functions over threshold, so
//! it cannot tell a moved runner from a moved function.

use core::fmt;

use quenchant_shape::shape::Maybe;

use super::Amount;
use super::Family;
use super::Policy;
use super::RowName;
use super::Run;
use super::Share;
use crate::check::SiteName;

/// The fewest functions both reports must time for a shift to be read.
const MIN_FUNCTIONS: usize = 10;

/// Millionths in one: the ratio of an unchanged amount.
const UNIT: u128 = 1_000_000;

/// Millionths in one hundredth of a percent, the unit a threshold is read in.
const PER_SHARE: u128 = 100;

/// Millionths in one tenth of a percent, the precision a ratio is written to.
const PER_TENTH: u128 = 1_000;

/// A head amount over its base's, in millionths: 1 000 000 is unchanged.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Ratio(u128);

/// Why no ratio is read: the base amount is zero, or the arithmetic
/// overflows.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Unmeasured;

/// Whether a ratio crosses a threshold.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Crossing
{
    /// The ratio grew by the threshold or more.
    Crosses,
    /// The ratio grew by less than the threshold, or fell.
    Within,
}

impl Ratio
{
    /// The ratio of `after` to `before`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `after × 1 000 000 ÷ before`, rounded down.
    /// - provides: one function's move, and the wall time's.
    /// - fails: [`Unmeasured`] when `before` is zero or the product overflows.
    /// - panics: none.
    /// - executable: none — the arithmetic is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the replayed run's functions and a function at zero;
    ///   a swapped side or a lost scale changes the shift.
    /// - witness: `judge::shift::tests::the_shift_is_the_median_over_every_function`
    fn between(
        before: Amount,
        after: Amount,
    ) -> Maybe<Self, Unmeasured>
    {
        after
            .0
            .checked_mul(UNIT)
            .and_then(|scaled| scaled.checked_div(before.0))
            .map_or(Maybe::Absent(Unmeasured), |ratio| {
                Maybe::Present(Self(ratio))
            })
    }

    /// This ratio divided by `shift`: `(1 + d) ÷ (1 + s)`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `self × 1 000 000 ÷ shift`, rounded down.
    /// - provides: a function's move with the runner's taken out.
    /// - fails: [`Unmeasured`] when the shift is zero or the product overflows.
    /// - panics: none.
    /// - executable: none — the arithmetic is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a function at +40 % beside a +2 % shift, and the
    ///   replayed run's `decide` at +31.8 % beside +27.2 %; reading the
    ///   absolute ratio files the second.
    /// - witness: `check::tests::a_uniform_timing_shift_is_a_runner_shift`
    fn beside(
        self,
        shift: Self,
    ) -> Maybe<Self, Unmeasured>
    {
        self.0
            .checked_mul(UNIT)
            .and_then(|scaled| scaled.checked_div(shift.0))
            .map_or(Maybe::Absent(Unmeasured), |ratio| {
                Maybe::Present(Self(ratio))
            })
    }

    /// Whether the ratio grew by `threshold` or more.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Crossing::Crosses`] exactly when the ratio is at least `1 +
    ///   threshold`; a threshold too large to represent is never crossed.
    /// - provides: the comparison every judgement of the shift makes.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the comparison is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a function just past 7.5 % and one just under it
    ///   beside the shift; a strict comparison or a threshold off by a scale
    ///   changes which files.
    /// - witness: `check::tests::a_uniform_timing_shift_is_a_runner_shift`
    fn crosses(
        self,
        threshold: Share,
    ) -> Crossing
    {
        match threshold
            .0
            .checked_mul(PER_SHARE)
            .and_then(|bound| bound.checked_add(UNIT))
        {
            Some(bound) if self.0 >= bound => Crossing::Crosses,
            Some(_) | None => Crossing::Within,
        }
    }
}

impl fmt::Display for Ratio
{
    /// Writes the change as a signed percentage, to the nearest tenth: `+27.2`,
    /// `-3`, `+0`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a rise with a tenth, a whole fall and no change; a
    ///   sign chosen at another bound or a lost tenth changes the row.
    /// - witness: `judge::shift::tests::a_ratio_is_written_as_its_change`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let tenths = self
            .0
            .abs_diff(UNIT)
            .saturating_add(PER_TENTH.div_euclid(2))
            .div_euclid(PER_TENTH);
        let sign = if self.0 < UNIT && tenths > 0 {
            "-"
        }
        else {
            "+"
        };
        let whole = tenths.div_euclid(10);
        match tenths.rem_euclid(10) {
            0 => write!(f, "{sign}{whole}"),
            tenth => write!(f, "{sign}{whole}.{tenth}"),
        }
    }
}

/// How many functions both reports time.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Functions(usize);

impl fmt::Display for Functions
{
    /// Writes the count.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the replayed run's row states 16 functions; an empty
    ///   write changes the row.
    /// - witness: `tests::cli::a_runner_shift_is_read_over_every_function`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{}", self.0)
    }
}

/// A run's global shift: the median ratio over every function both reports
/// time, and how many they are.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct GlobalShift
{
    /// The median ratio.
    pub ratio: Ratio,
    /// The functions it is the median of.
    pub functions: Functions,
}

/// Why no global shift is read for a failed timing check, so each function
/// files as the check names it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Unread
{
    /// The check holds no timing section: allocations are judged apart.
    Allocation,
    /// The check's summary names no base commit.
    Unnamed,
    /// The tree holds no policy for the benchmark, or it fails no check on
    /// timing.
    Unjudged,
    /// No run kept one side's full timing report.
    Unkept,
    /// Fewer than [`MIN_FUNCTIONS`] functions are timed on both sides.
    Few,
}

/// Why a regression is not the runner's: its section is no runner shift
/// ([`crate::check::Section::judged`]).
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Unshifted;

/// Why a policy yields no timing threshold: it fails no check on timing.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Untimed;

impl Policy
{
    /// The smallest timing change the policy fails a check on.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the `[functions.timing]` block's `min_percent_change`, or
    ///   hotpath's default, when the block judges and fails the check.
    /// - provides: the threshold a function's move beside the shift is judged
    ///   against.
    /// - fails: [`Untimed`] when the policy fails no check on timing.
    /// - panics: none.
    /// - executable: none — the lookup is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the repository's timing policy at 7.5 % and its
    ///   allocation policy, which judges no timing; another family's threshold
    ///   or a constant changes the reading.
    /// - witness: `judge::shift::tests::the_shift_is_the_median_over_every_function`
    pub(crate) fn timing_threshold(&self) -> Maybe<Share, Untimed>
    {
        self.families
            .iter()
            .find(|&&(family, _)| family == Family::Timing)
            .map_or(Maybe::Absent(Untimed), |&(_, ref judged)| {
                Maybe::Present(judged.change)
            })
    }
}

/// A failed timing check's two full reports, the global shift read over them
/// and the threshold its policy fails the check at.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Reading
{
    /// The base's report.
    base: Run,
    /// The head's report.
    head: Run,
    /// The policy's timing threshold.
    threshold: Share,
    /// The global shift.
    shift: GlobalShift,
}

impl Reading
{
    /// Reads the global shift of `head` against `base` under `policy`.
    ///
    /// # Specification
    /// - requires: `base` and `head` are the full timing reports of the check's
    ///   base and head.
    /// - ensures: the shift's ratio is the median of every timing row's average
    ///   ratio, over the rows both reports carry with a nonzero base average;
    ///   for an even count, the midpoint of the two middle ratios.
    /// - provides: the reading each site of the check is judged by.
    /// - fails: [`Unread::Unjudged`] when the policy fails no check on timing;
    ///   [`Unread::Few`] when fewer than [`MIN_FUNCTIONS`] rows are measured on
    ///   both sides.
    /// - panics: none.
    /// - executable: none — the median is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the replayed run's 16 functions, the same less seven
    ///   of them, and the allocation policy; the lower middle, the mean, a
    ///   function counted from one side only, or a shift read from nine
    ///   functions changes the reading.
    /// - witness: `judge::shift::tests::the_shift_is_the_median_over_every_function`
    #[inline]
    pub fn read(
        base: Run,
        head: Run,
        policy: &Policy,
    ) -> Maybe<Self, Unread>
    {
        let Maybe::Present(threshold) = policy.timing_threshold()
        else {
            return Maybe::Absent(Unread::Unjudged);
        };
        let mut ratios: Vec<Ratio> = head
            .rows
            .iter()
            .filter(|&(&(family, _), _)| family == Family::Timing)
            .filter_map(|(key, after)| {
                let before = base.rows.get(key)?;
                match Ratio::between(before.avg, after.avg) {
                    Maybe::Present(ratio) => Some(ratio),
                    Maybe::Absent(Unmeasured) => None,
                }
            })
            .collect();
        if ratios.len() < MIN_FUNCTIONS {
            return Maybe::Absent(Unread::Few);
        }
        ratios.sort_unstable();
        let upper = ratios.len().div_euclid(2);
        let lower = match ratios.len().rem_euclid(2) {
            0 => upper.saturating_sub(1),
            _ => upper,
        };
        let (Some(&Ratio(low)), Some(&Ratio(high))) = (ratios.get(lower), ratios.get(upper))
        else {
            return Maybe::Absent(Unread::Few);
        };
        Maybe::Present(Self {
            base,
            head,
            threshold,
            shift: GlobalShift {
                ratio: Ratio(low.midpoint(high)),
                functions: Functions(ratios.len()),
            },
        })
    }

    /// The global shift.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the replayed run's row states its shift; another
    ///   value changes the row.
    /// - witness: `tests::cli::a_runner_shift_is_read_over_every_function`
    #[must_use]
    #[inline]
    pub const fn shift(&self) -> GlobalShift
    {
        self.shift
    }

    /// Whether `site`'s move beside the shift crosses the threshold.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Crossing::Crosses`] when the site's average ratio divided
    ///   by the shift's crosses the threshold, and when either report lacks the
    ///   site or its ratio is unmeasured, so a function the reports cannot
    ///   judge files as the check names it.
    /// - provides: whether a site regressed.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the lookup and the comparison are the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a function at +40 % beside a +2 % shift, a function
    ///   at +8 % beside it, the replayed run's three sites, and a site neither
    ///   report times; the absolute ratio, a missing site read as within, or a
    ///   lost division changes which files.
    /// - witness: `check::tests::a_uniform_timing_shift_is_a_runner_shift`
    #[must_use]
    #[inline]
    pub fn site(
        &self,
        site: &SiteName,
    ) -> Crossing
    {
        let key = (Family::Timing, RowName(site.to_string()));
        let (Some(before), Some(after)) = (self.base.rows.get(&key), self.head.rows.get(&key))
        else {
            return Crossing::Crosses;
        };
        match Ratio::between(before.avg, after.avg) {
            Maybe::Present(ratio) => match ratio.beside(self.shift.ratio) {
                Maybe::Present(relative) => relative.crosses(self.threshold),
                Maybe::Absent(Unmeasured) => Crossing::Crosses,
            },
            Maybe::Absent(Unmeasured) => Crossing::Crosses,
        }
    }

    /// Whether the runner moved past the threshold: the wall time and the
    /// global shift both cross it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Crossing::Crosses`] exactly when both reports state a wall
    ///   time, its ratio crosses the threshold, and so does the shift's.
    /// - provides: the condition a runner shift adds to no site crossing.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the conjunction is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the replayed run (wall +28 %, shift +27 %) and a run
    ///   whose functions moved +2 %; reading either one alone changes whether
    ///   the second is a shift.
    /// - witness: `check::tests::a_uniform_timing_shift_is_a_runner_shift`
    #[must_use]
    #[inline]
    pub fn runner(&self) -> Crossing
    {
        let wall = match (self.base.wall, self.head.wall) {
            (Some(before), Some(after)) => match Ratio::between(before, after) {
                Maybe::Present(ratio) => ratio.crosses(self.threshold),
                Maybe::Absent(Unmeasured) => Crossing::Within,
            },
            (None, _) | (_, None) => Crossing::Within,
        };
        match (wall, self.shift.ratio.crosses(self.threshold)) {
            (Crossing::Crosses, Crossing::Crosses) => Crossing::Crosses,
            (Crossing::Crosses | Crossing::Within, Crossing::Within)
            | (Crossing::Within, Crossing::Crosses) => Crossing::Within,
        }
    }
}

#[cfg(test)]
mod tests
{
    use quenchant_shape::shape::Maybe;

    use super::super::Input;
    use super::super::Policy;
    use super::super::Run;
    use super::Functions;
    use super::Ratio;
    use super::Reading;
    use super::Unread;

    /// The replayed run's base report: `ac58445`'s `gandr-timing`.
    const BASE: &str = include_str!(
        "../../tests/reports/hotpath-ac58445989aee8c21905b9d91d7f9d18b0ab5427/gandr-timing.json"
    );

    /// The replayed run's head report: `73f2e46`'s `gandr-timing`.
    const HEAD: &str = include_str!(
        "../../tests/reports/hotpath-73f2e468d48dfd25332b479e7ee451195301e227/gandr-timing.json"
    );

    /// The repository's timing policy.
    const TIMING: &str = include_str!("../../../../hotpath/gandr-timing-policy.toml");

    /// The repository's allocation policy.
    const ALLOC: &str = include_str!("../../../../hotpath/gandr-policy.toml");

    #[test]
    fn the_shift_is_the_median_over_every_function()
    {
        let run = |text: &str| {
            Run::read(Input {
                path: "report.json",
                text,
            })
            .unwrap()
        };
        let policy = |text: &str| {
            Policy::read(Input {
                path: "policy.toml",
                text,
            })
            .unwrap()
        };
        let Maybe::Present(reading) = Reading::read(run(BASE), run(HEAD), &policy(TIMING))
        else {
            panic!("the replayed run reads a shift");
        };
        // The 8th and 9th of 16 sorted ratios: `lsp comment edit`
        // (34.94 → 44.24 ms, 1 266 170 millionths) and `closure check`
        // (130.43 → 166.57 ms, 1 277 083), their midpoint rounded down.
        assert_eq!(reading.shift().ratio, Ratio(1_271_626));
        assert_eq!(reading.shift().functions, Functions(16));
        assert_eq!(
            Reading::read(run(BASE), run(HEAD), &policy(ALLOC)),
            Maybe::Absent(Unread::Unjudged),
            "the allocation policy judges no timing"
        );
        let mut head: serde_json::Value = serde_json::from_str(HEAD).unwrap();
        let rows = head["functions_timing"]["data"].as_array_mut().unwrap();
        rows.truncate(9);
        assert_eq!(
            Reading::read(run(BASE), run(&head.to_string()), &policy(TIMING)),
            Maybe::Absent(Unread::Few),
            "nine functions in common read no shift"
        );
    }

    #[test]
    fn a_ratio_is_written_as_its_change()
    {
        assert_eq!(Ratio(1_271_626).to_string(), "+27.2");
        assert_eq!(Ratio(970_000).to_string(), "-3");
        assert_eq!(Ratio(1_000_000).to_string(), "+0");
        assert_eq!(
            Ratio(999_960).to_string(),
            "+0",
            "a fall that rounds to none is no change"
        );
    }
}
