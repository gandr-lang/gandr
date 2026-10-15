//! Samples charged to the specification checks on their stacks, and the
//! ranking they add up to.

extern crate alloc;

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::fmt;
use core::num::NonZeroU32;
use core::num::NonZeroU64;
use core::num::NonZeroUsize;
use core::str::FromStr;
use std::path::Path;
use std::path::PathBuf;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::region::ItemName;
use crate::region::Line;
use crate::region::Region;
use crate::region::Regions;
use crate::select::Workload;
use crate::stack::Body;
use crate::stack::Frame;

/// What a sample's stack was doing, by the checks on it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Charge<'regions>
{
    /// At least one frame runs a specification check.
    Check
    {
        /// The outermost check: the one whose evaluation caused the sampled
        /// work.
        charged: &'regions Region,
        /// The innermost check: the one executing.
        innermost: &'regions Region,
    },
    /// No frame runs a specification check.
    Elsewhere,
}

/// The checks on a sampled stack.
///
/// # Specification
/// - requires: `frames` innermost first, as perf prints them.
/// - ensures: a frame whose line lies in a specification attribute is a check,
///   unless the frame inside it enters a body through `eval_once`: anodized
///   spans the call into the body with the attribute's lines. The outermost
///   such frame is charged and the innermost reported.
/// - provides: the attribution every ranking adds up.
/// - panics: none.
/// - executable: none — the charge is the walk over the frames and the
///   attribute table; a predicate could only repeat it.
///
/// # Adequacy
/// - hypothesis: L3 — a check nested inside another's evaluation, a body
///   reached through its attribute line, and a stack with no check; charging
///   the innermost, counting the body, or charging a stack without a check
///   changes the asserted charge.
/// - witness: `ledger::tests::a_body_under_its_attribute_line_is_not_a_check`
/// - witness: `ledger::tests::the_outermost_check_is_charged`
#[inline]
#[must_use]
pub fn charge<'regions>(
    frames: &[Frame],
    regions: &'regions Regions,
) -> Charge<'regions>
{
    let mut innermost = None;
    let mut outermost = None;
    let mut inside = Body::Elsewhere;
    for frame in frames {
        if inside == Body::Elsewhere
            && let Maybe::Present(ref location) = frame.location
            && let Maybe::Present(region) = regions.find(&location.file, location.line)
        {
            innermost.get_or_insert(region);
            outermost = Some(region);
        }
        inside = frame.symbol.body();
    }
    match (outermost, innermost) {
        (Some(charged), Some(innermost)) => Charge::Check { charged, innermost },
        (Some(_) | None, _) => Charge::Elsewhere,
    }
}

/// A number of samples.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct SampleCount(u64);

/// A quantity in tenths, printed with one decimal and padded as the format
/// asks.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Tenths(u64);

impl Tenths
{
    /// `part` over `whole`, scaled by `scale` and rounded to the nearest
    /// tenth; zero when `whole` is.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: ⌊(10 · scale · part + whole / 2) / whole⌋ tenths, saturating.
    /// - provides: the shares and seconds the report prints, without floating
    ///   point.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — shares of 20 samples, two thirds rounding up, and
    ///   seconds at 2 Hz; truncation or a dropped scale changes the table.
    /// - witness: `ledger::tests::the_ranking_orders_checks_by_charged_time`
    #[spec(ensures: |ret| whole.0 != 0 || ret.0 == 0)]
    fn ratio(
        part: SampleCount,
        whole: SampleCount,
        scale: SampleCount,
    ) -> Self
    {
        let numerator = part
            .0
            .saturating_mul(scale.0)
            .saturating_mul(10)
            .saturating_add(whole.0.checked_div(2).unwrap_or(0));
        Self(numerator.checked_div(whole.0).unwrap_or(0))
    }
}

impl fmt::Display for Tenths
{
    /// Writes the quantity with one decimal, honouring width and alignment.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let whole = self.0.checked_div(10).unwrap_or(0);
        let tenth = self.0.checked_rem(10).unwrap_or(0);
        f.pad(&format!("{whole}.{tenth}"))
    }
}

/// The sampling rate, in samples per second; never zero.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Frequency(NonZeroU32);

impl FromStr for Frequency
{
    type Err = core::num::ParseIntError;

    /// Reads a positive decimal rate.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the rate `text` spells, when it is a positive integer.
    /// - provides: the `--frequency` argument.
    /// - fails: the parse error of a non-number or of zero.
    /// - panics: none.
    /// - executable: none — the outcome is `NonZeroU32`'s own parse.
    ///
    /// # Errors
    /// A [`core::num::ParseIntError`] for anything but a positive integer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the rate reaches `perf record` and scales the
    ///   reported seconds; a dropped or ignored rate changes both.
    /// - witness: `cli::cli::a_profile_is_charged_to_its_outermost_specification`
    #[inline]
    fn from_str(text: &str) -> Result<Self, Self::Err>
    {
        text.parse().map(Self)
    }
}

impl fmt::Display for Frequency
{
    /// Writes the rate in decimal, as `perf record -F` reads it.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        fmt::Display::fmt(&self.0, f)
    }
}

/// How many checks the report lists; never zero.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RankLimit(NonZeroUsize);

impl FromStr for RankLimit
{
    type Err = core::num::ParseIntError;

    /// Reads a positive decimal count.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the count `text` spells, when it is a positive integer.
    /// - provides: the `--top` argument.
    /// - fails: the parse error of a non-number or of zero.
    /// - panics: none.
    /// - executable: none — the outcome is `NonZeroUsize`'s own parse.
    ///
    /// # Errors
    /// A [`core::num::ParseIntError`] for anything but a positive integer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a limit of one prints one row; a limit that is
    ///   ignored prints them all.
    /// - witness: `ledger::tests::the_ranking_orders_checks_by_charged_time`
    #[inline]
    fn from_str(text: &str) -> Result<Self, Self::Err>
    {
        text.parse().map(Self)
    }
}

impl From<RankLimit> for usize
{
    /// The count the limit carries.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(limit: RankLimit) -> Self
    {
        limit.0.get()
    }
}

/// One profiled test's samples.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct TestTally
{
    /// Every sample.
    samples: SampleCount,
    /// The samples with a check on their stack.
    checking: SampleCount,
}

/// One check's samples.
#[derive(Clone, Debug, Eq, PartialEq)]
struct CheckTally
{
    /// The item the check specifies.
    item: ItemName,
    /// The samples it was the outermost check of.
    charged: SampleCount,
    /// The samples it was the innermost check of.
    innermost: SampleCount,
    /// The tests it was charged in.
    tests: BTreeSet<Workload>,
}

/// Every recorded sample, per test and per check.
///
/// # Specification
/// - provides: the totals a ranking prints; a check is keyed by its file and
///   first line.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Ledger
{
    /// Per profiled test.
    tests: BTreeMap<Workload, TestTally>,
    /// Per check, by file and first line.
    checks: BTreeMap<(PathBuf, Line), CheckTally>,
}

impl Ledger
{
    /// Adds one sample of `workload`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the test's sample count grows by one; for a check, its
    ///   checking count, the charged check's charged count and the innermost
    ///   check's innermost count each grow by one, and the charged check
    ///   records the test.
    /// - provides: the per-sample step of a profile.
    /// - panics: none.
    /// - executable: none — the counts are private and read back only through
    ///   the ranking.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — samples of two tests, nested and single checks and
    ///   none; a count added to the wrong check or test changes the ranking.
    /// - witness: `ledger::tests::the_ranking_orders_checks_by_charged_time`
    #[inline]
    pub fn record(
        &mut self,
        workload: &Workload,
        charge: Charge<'_>,
    )
    {
        let test = self.tests.entry(workload.clone()).or_default();
        test.samples.0 = test.samples.0.saturating_add(1);
        let Charge::Check { charged, innermost } = charge
        else {
            return;
        };
        test.checking.0 = test.checking.0.saturating_add(1);
        let fresh = |region: &Region| CheckTally {
            item: region.item.clone(),
            charged: SampleCount::default(),
            innermost: SampleCount::default(),
            tests: BTreeSet::new(),
        };
        let outer = self
            .checks
            .entry((charged.file.clone(), charged.first))
            .or_insert_with(|| fresh(charged));
        outer.charged.0 = outer.charged.0.saturating_add(1);
        outer.tests.insert(workload.clone());
        let inner = self
            .checks
            .entry((innermost.file.clone(), innermost.first))
            .or_insert_with(|| fresh(innermost));
        inner.innermost.0 = inner.innermost.0.saturating_add(1);
    }
}

/// The report a ledger reads as: each test's share of checking, then the
/// checks by charged time.
#[derive(Clone, Copy, Debug)]
pub struct Ranking<'ledger>
{
    /// The samples.
    pub ledger: &'ledger Ledger,
    /// The rate they were taken at.
    pub frequency: Frequency,
    /// The workspace root, stripped from the printed paths.
    pub root: &'ledger Path,
    /// How many checks to list.
    pub top: RankLimit,
}

impl fmt::Display for Ranking<'_>
{
    /// Writes the per-test table and the ranked checks.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one row per profiled test with its sampled seconds and the
    ///   share spent under a check; then at most `top` checks charged at least
    ///   one sample, by descending charged count and then by location, each
    ///   with its charged seconds, its share of every sample, its innermost
    ///   seconds, the number of tests it was charged in, its location relative
    ///   to `root` and its item.
    /// - provides: the worklist a reviewer fixes from.
    /// - fails: propagates the formatter's own write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two tests, three checks of which one is only ever
    ///   innermost, and a limit below the check count; a wrong order, share,
    ///   scale or limit changes the asserted text.
    /// - witness: `ledger::tests::the_ranking_orders_checks_by_charged_time`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let rate = SampleCount(NonZeroU64::from(self.frequency.0).get());
        let one = SampleCount(1);
        let hundred = SampleCount(100);
        let seconds = |samples| Tenths::ratio(samples, rate, one);
        let names: Vec<String> = self.ledger.tests.keys().map(ToString::to_string).collect();
        let width = names
            .iter()
            .map(|name| name.chars().count())
            .max()
            .unwrap_or(0)
            .max(4);
        writeln!(f, "profiled at {} Hz", self.frequency)?;
        writeln!(f, "{:<width$}  sampled  in checks", "test")?;
        let mut total = SampleCount::default();
        for (name, tally) in names.iter().zip(self.ledger.tests.values()) {
            total.0 = total.0.saturating_add(tally.samples.0);
            writeln!(
                f,
                "{name:<width$}  {:>5} s  {:>8}%",
                seconds(tally.samples),
                Tenths::ratio(tally.checking, tally.samples, hundred)
            )?;
        }
        let mut ranked: Vec<_> = self
            .ledger
            .checks
            .iter()
            .filter(|&(_, tally)| tally.charged.0 > 0)
            .collect();
        ranked.sort_by(|left, right| {
            right
                .1
                .charged
                .cmp(&left.1.charged)
                .then_with(|| left.0.cmp(right.0))
        });
        writeln!(
            f,
            "\nchecks by charged time: the outermost check on each sampled stack; innermost is the time \
             the check itself was running\nrank  charged   share  innermost  tests  check"
        )?;
        for (rank, &(&(ref file, first), tally)) in ranked.iter().take(self.top.0.get()).enumerate()
        {
            writeln!(
                f,
                "{:>4}  {:>5} s  {:>5}%  {:>7} s  {:>5}  {}:{first}  {}",
                rank.saturating_add(1),
                seconds(tally.charged),
                Tenths::ratio(tally.charged, total, hundred),
                seconds(tally.innermost),
                tally.tests.len(),
                file.strip_prefix(self.root).unwrap_or(file).display(),
                tally.item,
            )?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests
{
    use std::path::Path;

    use quenchant_shape::shape::Maybe;

    use super::Charge;
    use super::Ledger;
    use super::Ranking;
    use super::charge;
    use crate::region::ItemName;
    use crate::region::Line;
    use crate::region::Region;
    use crate::region::Regions;
    use crate::region::SourceText;
    use crate::stack::Frame;
    use crate::stack::Location;
    use crate::stack::Symbol;
    use crate::stack::position;

    /// A file with a check on line 2 calling a helper whose check is on line
    /// 6, both with bodies below their attributes.
    const SOURCE: &str = "\n\
        #[spec(ensures: |ret| helper(ret))]\n\
        fn outer() -> u8 { 1 }\n\
        \n\
        \n\
        #[spec(ensures: |ret| ret)]\n\
        fn helper(_: u8) -> bool { true }\n";

    #[test]
    fn the_outermost_check_is_charged()
    {
        let mut regions = Regions::default();
        regions
            .insert_source(Path::new("/ws/src/lib.rs"), SourceText::from(SOURCE))
            .unwrap();
        let frame = |symbol: &str, line| Frame {
            symbol: Symbol::from(symbol),
            location: Maybe::Present(Location {
                file: Path::new("/ws/src/lib.rs").to_path_buf(),
                line: Line::from(line),
            }),
        };
        let unknown = Frame {
            symbol: Symbol::from("core::iter::find"),
            location: Maybe::Absent(position::Absent::Unknown),
        };
        let item = |found: Charge<'_>| match found {
            Charge::Check { charged, innermost } => (charged.item.clone(), innermost.item.clone()),
            Charge::Elsewhere => (ItemName::from("-"), ItemName::from("-")),
        };
        assert_eq!(
            item(charge(
                &[
                    unknown.clone(),
                    frame("helper", 6),
                    frame("{closure#0}", 2),
                    frame("outer", 3)
                ],
                &regions
            )),
            (ItemName::from("outer"), ItemName::from("helper")),
            "a helper's check inside the outer check's evaluation: the outer is charged"
        );
        assert_eq!(
            item(charge(&[frame("helper", 6), frame("main", 9)], &regions)),
            (ItemName::from("helper"), ItemName::from("helper")),
            "a single check is both"
        );
        assert_eq!(
            charge(&[unknown, frame("helper", 7), frame("main", 9)], &regions),
            Charge::Elsewhere,
            "a body line is no check"
        );
    }

    #[test]
    fn a_body_under_its_attribute_line_is_not_a_check()
    {
        let mut regions = Regions::default();
        regions
            .insert_source(Path::new("/ws/src/lib.rs"), SourceText::from(SOURCE))
            .unwrap();
        let frame = |symbol: &str, line| Frame {
            symbol: Symbol::from(symbol),
            location: Maybe::Present(Location {
                file: Path::new("/ws/src/lib.rs").to_path_buf(),
                line: Line::from(line),
            }),
        };
        let body = Frame {
            symbol: Symbol::from("anodized::__::eval_once::<u8, outer::{closure#1}>"),
            location: Maybe::Absent(position::Absent::Unknown),
        };
        let inlined = Frame {
            symbol: Symbol::from("eval_once<u8, outer::{closure_env#1}>"),
            location: Maybe::Absent(position::Absent::Unknown),
        };
        let clause = Frame {
            symbol: Symbol::from("anodized::__::eval::<bool, outer::{closure#2}>"),
            location: Maybe::Absent(position::Absent::Unknown),
        };
        assert_eq!(
            charge(&[frame("work", 9), body, frame("outer", 2)], &regions),
            Charge::Elsewhere,
            "the call into the body carries the attribute's line and is not a check"
        );
        assert_eq!(
            charge(&[frame("work", 9), inlined, frame("outer", 2)], &regions),
            Charge::Elsewhere,
            "nor through an inlined `eval_once`"
        );
        assert!(
            matches!(
                charge(&[frame("work", 9), clause, frame("outer", 2)], &regions),
                Charge::Check { .. }
            ),
            "a clause's `eval` is the check itself"
        );
    }

    #[test]
    fn the_ranking_orders_checks_by_charged_time()
    {
        let region = |file: &str, first, item: &str| Region {
            file: Path::new("/ws").join(file),
            first: Line::from(first),
            last: Line::from(first),
            item: ItemName::from(item),
        };
        let scan = region("crates/a/src/lib.rs", 10, "Stack::top");
        let walk = region("crates/a/src/lib.rs", 40, "Stack::walk");
        let leaf = region("crates/b/src/lib.rs", 5, "leaf");
        let first = "gandr-a pick::first".parse().unwrap();
        let second = "gandr-b::tests big::one".parse().unwrap();
        let mut ledger = Ledger::default();
        let mut record = |workload, charge, times: u32| {
            for _ in 0 .. times {
                ledger.record(workload, charge);
            }
        };
        record(
            &first,
            Charge::Check {
                charged: &scan,
                innermost: &scan,
            },
            4,
        );
        record(
            &first,
            Charge::Check {
                charged: &scan,
                innermost: &leaf,
            },
            2,
        );
        record(&first, Charge::Elsewhere, 2);
        record(
            &second,
            Charge::Check {
                charged: &walk,
                innermost: &walk,
            },
            6,
        );
        record(
            &second,
            Charge::Check {
                charged: &scan,
                innermost: &scan,
            },
            2,
        );
        record(&second, Charge::Elsewhere, 4);
        let ranking = |top: &str| {
            Ranking {
                ledger: &ledger,
                frequency: "2".parse().unwrap(),
                root: Path::new("/ws"),
                top: top.parse().unwrap(),
            }
            .to_string()
        };
        let header = "profiled at 2 Hz\n\
            test                     sampled  in checks\n\
            gandr-a pick::first        4.0 s      75.0%\n\
            gandr-b::tests big::one    6.0 s      66.7%\n\
            \n\
            checks by charged time: the outermost check on each sampled stack; innermost is the time \
            the check itself was running\n\
            rank  charged   share  innermost  tests  check\n";
        assert_eq!(
            ranking("5"),
            format!(
                "{header}   \
                 1    4.0 s   40.0%      3.0 s      2  crates/a/src/lib.rs:10  Stack::top\n   \
                 2    3.0 s   30.0%      3.0 s      1  crates/a/src/lib.rs:40  Stack::walk\n"
            ),
            "charged order across tests, shares of all 20 samples, seconds at 2 Hz; the leaf is only \
             ever innermost and is not ranked"
        );
        assert_eq!(
            ranking("1"),
            format!(
                "{header}   1    4.0 s   40.0%      3.0 s      2  crates/a/src/lib.rs:10  Stack::top\n"
            ),
            "the limit"
        );
    }
}
