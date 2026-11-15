//! Each test's enforcing time over its plain time, read from two nextest JUnit
//! reports.
//!
//! The enforcing lane times every test with its specifications checked; the
//! plain baseline times the same tests with the checks compiled out. A test's
//! ratio is the factor its checks multiply its time by, which is what the
//! enforcing lane pays for that test's specifications. Tests pair by binary
//! and name; a test only one report times is counted, never compared.
//!
//! A ratio is flagged at or above a threshold, on a test that takes at least
//! the floor enforcing. Below the floor a test's time is mostly the process it
//! runs in, and its ratio says little about its checks. A time under a
//! millisecond, the reports' resolution, reads as one millisecond.
//!
//! **Threshold.** The binary flags at 4×, a test whose checks take three
//! quarters of its enforcing time. `mise run ci:spec-cost` ranks the slowest
//! enforcing tests by the share of their samples spent in checks. The tests
//! whose hottest checks walk what their functions accumulate spend from three
//! quarters to nearly all of their samples there, ratios from 4 to over 30;
//! the tests whose checks are bounded spend about half, ratios near 2. The
//! threshold sits between the two groups, so a clause that starts walking
//! moves its test across it. The floor, a quarter second, leaves out the tests
//! whose time is mostly their process. The reversal is a ranking whose
//! check-dominated tests fall below 4×, which lowers the threshold.

extern crate alloc;

use alloc::collections::BTreeMap;
use core::convert::Infallible;
use core::fmt;
use core::num::ParseIntError;
use core::str::FromStr;
use core::time::Duration;
use std::path::Path;

use anodized::spec;
use gandr_workflow_test_timing::report::BinaryId;
use gandr_workflow_test_timing::report::ReportText;
use gandr_workflow_test_timing::report::TestName;
use gandr_workflow_test_timing::report::samples;

use crate::error::CostError;
use crate::ledger::RankLimit;

/// The least time a report resolves: nextest writes milliseconds.
const RESOLUTION: Duration = Duration::from_millis(1);

/// A ratio of two times in hundredths: `250` is two and a half times.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Factor(u128);

impl Factor
{
    /// `over` divided by `under`, in hundredths rounded down, each time read
    /// as at least a millisecond.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: ⌊100 · max(over, 1 ms) / max(under, 1 ms)⌋, saturating;
    ///   exactly one when the two times read alike.
    /// - provides: every ratio the report prints and flags, without floating
    ///   point.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two and a half seconds over one, a third, two times
    ///   below the resolution and a recorded pair; truncation upward, a swapped
    ///   quotient or a zero divisor changes the asserted factor.
    /// - witness: `ratio::tests::a_factor_is_hundredths_of_the_quotient`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| over.max(RESOLUTION) != under.max(RESOLUTION) || ret == Self(100_u128))]
    pub fn of(
        over: Duration,
        under: Duration,
    ) -> Self
    {
        let over = over.max(RESOLUTION).as_nanos();
        let under = under.max(RESOLUTION).as_nanos();
        Self(
            over.saturating_mul(100_u128)
                .checked_div(under)
                .unwrap_or(u128::MAX),
        )
    }
}

impl FromStr for Factor
{
    type Err = CostError;

    /// Reads a ratio written in decimal with at most two decimals.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the ratio `text` spells as digits, optionally followed by a
    ///   point and one or two digits.
    /// - provides: the `--threshold` argument.
    /// - fails: [`CostError::Factor`] for anything else, or a ratio past the
    ///   representable range.
    /// - panics: none.
    /// - executable: none — the parse is its own specification; a predicate
    ///   could only repeat it.
    ///
    /// # Errors
    /// [`CostError::Factor`] — `text` is not such a ratio.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a whole ratio, one and two decimals, three decimals,
    ///   a bare point, a missing whole part and a letter; reading tenths as
    ///   hundredths or accepting a third decimal changes the asserted value.
    /// - witness: `ratio::tests::a_threshold_reads_at_most_two_decimals`
    #[inline]
    fn from_str(text: &str) -> Result<Self, Self::Err>
    {
        let refuse = || CostError::Factor {
            text: text.to_owned(),
        };
        let (whole, fraction) = text.split_once('.').unwrap_or((text, ""));
        if whole.is_empty()
            || fraction.len() > 2
            || (text.contains('.') && fraction.is_empty())
            || !whole
                .bytes()
                .chain(fraction.bytes())
                .all(|byte| byte.is_ascii_digit())
        {
            return Err(refuse());
        }
        let whole = whole.parse::<u128>().ok().ok_or_else(refuse)?;
        let hundredths = format!("{fraction:0<2}")
            .parse::<u128>()
            .ok()
            .ok_or_else(refuse)?;
        whole
            .checked_mul(100_u128)
            .and_then(|scaled| scaled.checked_add(hundredths))
            .map(Self)
            .ok_or_else(refuse)
    }
}

impl fmt::Display for Factor
{
    /// Writes the ratio with two decimals and a times sign.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the whole part, a point, the two hundredths digits and
    ///   `×`.
    /// - provides: the ratio column and the threshold the report states.
    /// - fails: propagates the formatter's own write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a recorded pair's factor and a whole threshold render
    ///   exactly; a dropped leading zero changes the text.
    /// - witness: `ratio::tests::a_factor_is_hundredths_of_the_quotient`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let whole = self.0.checked_div(100_u128).unwrap_or(0_u128);
        let hundredths = self.0.checked_rem(100_u128).unwrap_or(0_u128);
        write!(f, "{whole}.{hundredths:02}×")
    }
}

/// The least enforcing time a flagged test takes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Floor(Duration);

impl FromStr for Floor
{
    type Err = CostError;

    /// Reads a non-negative number of seconds.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the duration `text` spells in decimal seconds.
    /// - provides: the `--floor` argument.
    /// - fails: [`CostError::Seconds`] for a non-number, a negative or
    ///   unrepresentable number of seconds.
    /// - panics: none.
    /// - executable: none — the outcome is `Duration`'s own conversion.
    ///
    /// # Errors
    /// [`CostError::Seconds`] — `text` is not such a number.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a quarter second, a whole second, a negative number
    ///   and a word; a scale other than seconds changes the asserted floor.
    /// - witness: `ratio::tests::a_floor_reads_seconds`
    #[inline]
    fn from_str(text: &str) -> Result<Self, Self::Err>
    {
        text.parse::<f64>()
            .ok()
            .and_then(|seconds| Duration::try_from_secs_f64(seconds).ok())
            .map(Self)
            .ok_or_else(|| CostError::Seconds {
                text: text.to_owned(),
            })
    }
}

impl fmt::Display for Floor
{
    /// Writes the floor in seconds.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        fmt::Display::fmt(&Seconds(self.0), f)
    }
}

/// A time printed in seconds with three decimals, the reports' resolution.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Seconds(Duration);

impl fmt::Display for Seconds
{
    /// Writes the time in seconds with three decimals.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{:.3} s", self.0.as_secs_f64())
    }
}

/// The commit a plain baseline timed.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Commit(String);

impl FromStr for Commit
{
    type Err = Infallible;

    /// Adopts `text` as given.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from_str(text: &str) -> Result<Self, Self::Err>
    {
        Ok(Self(text.to_owned()))
    }
}

impl fmt::Display for Commit
{
    /// Writes the commit as given.
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

/// How many whole hours before a report its baseline ran.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Hours(u64);

impl FromStr for Hours
{
    type Err = ParseIntError;

    /// Reads a decimal count of hours.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from_str(text: &str) -> Result<Self, Self::Err>
    {
        text.parse().map(Self)
    }
}

impl fmt::Display for Hours
{
    /// Writes the count in decimal.
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

/// The plain run a report divides by.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Baseline
{
    /// The commit it timed.
    pub commit: Commit,
    /// How long before the enforcing run it ran.
    pub age: Hours,
}

/// A number of tests.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Eq, Ord, PartialEq, PartialOrd)]
pub struct TestCount(usize);

impl From<usize> for TestCount
{
    /// Adopts `count` as given.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: usize) -> Self
    {
        Self(count)
    }
}

impl fmt::Display for TestCount
{
    /// Writes the count in decimal.
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

/// One test timed in both reports.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Comparison
{
    /// The binary the test ran in.
    pub binary: BinaryId,
    /// The test's path inside its binary.
    pub test: TestName,
    /// Its time in the plain report.
    pub plain: Duration,
    /// Its time in the enforcing report.
    pub enforcing: Duration,
}

impl Comparison
{
    /// The test's enforcing time over its plain time.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    #[must_use]
    pub fn factor(&self) -> Factor
    {
        Factor::of(self.enforcing, self.plain)
    }
}

/// Both reports' tests, paired by binary and name.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct Pairing
{
    /// The tests both reports time, by descending factor, then by binary and
    /// name.
    pub compared: Vec<Comparison>,
    /// How many tests only the enforcing report times.
    pub enforcing_only: TestCount,
    /// How many tests only the plain report times.
    pub plain_only: TestCount,
}

/// Each test's time in one report, the longer when it is timed twice.
///
/// # Specification
/// - requires: nothing — any text is admissible input.
/// - ensures: one entry per binary and test name the report times, holding its
///   longest time.
/// - provides: one side of [`pair`].
/// - fails: the refusals of [`samples`], naming `path`.
/// - panics: none.
/// - executable: none — the outcome is the report's own content, which only the
///   read itself recovers.
///
/// # Errors
/// [`CostError::Timing`] — the report is not one nextest wrote.
///
/// # Adequacy
/// - hypothesis: L3 — a report that times one test twice keeps the longer time;
///   keeping the first or the sum changes the asserted pairing.
/// - witness: `ratio::tests::tests_pair_by_binary_and_name`
fn times(
    text: ReportText<'_>,
    path: &Path,
) -> Result<BTreeMap<(BinaryId, TestName), Duration>, CostError>
{
    let mut times = BTreeMap::new();
    for sample in samples(text, path)? {
        let time = times
            .entry((sample.binary, sample.test))
            .or_insert(Duration::ZERO);
        *time = (*time).max(sample.elapsed);
    }
    Ok(times)
}

/// Pairs the tests of a plain and an enforcing report.
///
/// # Specification
/// - requires: nothing — any text is admissible input.
/// - ensures: one [`Comparison`] per binary and test name both reports time,
///   with each report's longer time when it times the test twice, by descending
///   factor and then by binary and name; the tests one report times alone are
///   counted.
/// - provides: what [`Comparisons`] renders.
/// - fails: the refusals of [`samples`] for either report, naming its path.
/// - panics: none.
///
/// # Errors
/// [`CostError::Timing`] — a report is not one nextest wrote.
///
/// # Adequacy
/// - hypothesis: L3 — one test name in two binaries, a test in each report
///   alone, a test timed twice and a tie in factor; pairing by name alone,
///   dropping a count, keeping the shorter time or ordering ascending changes
///   the asserted pairing.
/// - witness: `ratio::tests::tests_pair_by_binary_and_name`
/// - witness: `tests::ratio::a_recorded_pair_reports_each_test_against_the_baseline`
#[inline]
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |pairing| pairing
    .compared
    .is_sorted_by(|higher, lower| higher.factor() >= lower.factor())))]
pub fn pair(
    plain: ReportText<'_>,
    plain_path: &Path,
    enforcing: ReportText<'_>,
    enforcing_path: &Path,
) -> Result<Pairing, CostError>
{
    let plain = times(plain, plain_path)?;
    let mut enforcing = times(enforcing, enforcing_path)?;
    let mut compared = Vec::with_capacity(plain.len());
    let mut plain_only = 0_usize;
    for (key, plain_time) in plain {
        if let Some(enforcing_time) = enforcing.remove(&key) {
            let (binary, test) = key;
            compared.push(Comparison {
                binary,
                test,
                plain: plain_time,
                enforcing: enforcing_time,
            });
        }
        else {
            plain_only = plain_only.saturating_add(1);
        }
    }
    compared.sort_by(|left, right| {
        right
            .factor()
            .cmp(&left.factor())
            .then_with(|| (&left.binary, &left.test).cmp(&(&right.binary, &right.test)))
    });
    Ok(Pairing {
        compared,
        enforcing_only: TestCount(enforcing.len()),
        plain_only: TestCount(plain_only),
    })
}

/// The report a pairing reads as, in Markdown: the baseline it divides by,
/// the tests by ratio, and the totals.
#[derive(Clone, Copy, Debug)]
pub struct Comparisons<'pairing>
{
    /// The paired tests.
    pub pairing: &'pairing Pairing,
    /// The plain run they divide by.
    pub baseline: &'pairing Baseline,
    /// The ratio a flagged test reaches.
    pub threshold: Factor,
    /// The enforcing time a flagged test reaches.
    pub floor: Floor,
    /// How many tests to list, besides every flagged one.
    pub top: RankLimit,
}

impl fmt::Display for Comparisons<'_>
{
    /// Writes the baseline, the table of tests by ratio and the totals.
    ///
    /// # Specification
    /// - requires: `pairing` ordered as [`pair`] orders it.
    /// - ensures: names the baseline's commit and age, the threshold and the
    ///   floor; lists, by descending factor, the tests taking at least the
    ///   floor enforcing, as many as `top` or as are flagged, whichever is
    ///   more, each with its plain and enforcing times, its factor and whether
    ///   it is flagged; then counts the tests both reports time with their
    ///   total times and overall factor, the flagged tests, and the tests one
    ///   report times alone.
    /// - provides: the job summary and the artifact a reviewer reads.
    /// - fails: propagates the formatter's own write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a short test with the highest ratio, more flagged
    ///   tests than the limit, an unflagged slow test and an empty table; a
    ///   floor that is ignored, a limit that cuts a flagged test, or a total
    ///   over the wrong tests changes the asserted text.
    /// - witness: `ratio::tests::the_report_lists_every_flagged_test_above_the_floor`
    /// - witness: `tests::ratio::a_recorded_pair_reports_each_test_against_the_baseline`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let compared = &self.pairing.compared;
        writeln!(
            f,
            "### Specification cost per test\n\nEach test's time with its specifications \
             enforced over its time without them: this run's enforcing report over the plain \
             baseline of `main` at `{}`, {} h old. A ratio of {} or more on a test taking at \
             least {} enforcing is flagged.\n",
            self.baseline.commit, self.baseline.age, self.threshold, self.floor
        )?;
        let measured: Vec<&Comparison> = compared
            .iter()
            .filter(|comparison| comparison.enforcing >= self.floor.0)
            .collect();
        let flagged = measured
            .iter()
            .filter(|comparison| comparison.factor() >= self.threshold)
            .count();
        if measured.is_empty() {
            writeln!(f, "No test takes {} or more enforcing.\n", self.floor)?;
        }
        else {
            writeln!(
                f,
                "| Test | Plain | Enforcing | Ratio | |\n| --- | ---: | ---: | ---: | --- |"
            )?;
            for comparison in measured.iter().take(flagged.max(usize::from(self.top))) {
                let factor = comparison.factor();
                writeln!(
                    f,
                    "| `{} {}` | {} | {} | {factor} | {} |",
                    comparison.binary,
                    comparison.test,
                    Seconds(comparison.plain),
                    Seconds(comparison.enforcing),
                    if factor >= self.threshold {
                        "flagged"
                    }
                    else {
                        ""
                    }
                )?;
            }
            writeln!(f)?;
        }
        let plain = compared.iter().fold(Duration::ZERO, |sum, comparison| {
            sum.saturating_add(comparison.plain)
        });
        let enforcing = compared.iter().fold(Duration::ZERO, |sum, comparison| {
            sum.saturating_add(comparison.enforcing)
        });
        writeln!(
            f,
            "{} tests in both reports: {} plain, {} enforcing, {} overall; {} flagged. {} only \
             in the enforcing report, {} only in the plain baseline.",
            compared.len(),
            Seconds(plain),
            Seconds(enforcing),
            Factor::of(enforcing, plain),
            flagged,
            self.pairing.enforcing_only,
            self.pairing.plain_only
        )
    }
}

#[cfg(test)]
mod tests
{
    use core::time::Duration;
    use std::path::Path;

    use gandr_workflow_test_timing::report::ReportText;

    use super::Baseline;
    use super::Commit;
    use super::Comparison;
    use super::Comparisons;
    use super::Factor;
    use super::Floor;
    use super::Hours;
    use super::Pairing;
    use super::TestCount;
    use super::pair;
    use crate::error::CostError;
    use crate::ledger::RankLimit;

    #[test]
    fn a_factor_is_hundredths_of_the_quotient()
    {
        let seconds = Duration::from_secs;
        let millis = Duration::from_millis;
        assert_eq!(Factor::of(millis(2_500), seconds(1)), Factor(250));
        assert_eq!(
            Factor::of(seconds(1), seconds(3)),
            Factor(33),
            "rounded down"
        );
        assert_eq!(
            Factor::of(Duration::ZERO, Duration::from_micros(400)),
            Factor(100),
            "both below the resolution read as one millisecond"
        );
        assert_eq!(Factor::of(millis(50), Duration::ZERO), Factor(5_000));
        let recorded = Factor::of(millis(7_020), millis(128));
        assert_eq!(recorded, Factor(5_484));
        assert_eq!(recorded.to_string(), "54.84×");
        assert_eq!(Factor(300).to_string(), "3.00×");
        assert_eq!(Factor(5).to_string(), "0.05×");
    }

    #[test]
    fn a_threshold_reads_at_most_two_decimals()
    {
        for (text, expected) in [("3", 300), ("2.5", 250), ("2.25", 225), ("0", 0)] {
            assert_eq!(text.parse::<Factor>(), Ok(Factor(expected)), "{text}");
        }
        for text in ["2.505", "", ".5", "2.", "a", "1.x", "-1", "1e3"] {
            assert_eq!(
                text.parse::<Factor>(),
                Err(CostError::Factor { text: text.into() }),
                "{text}"
            );
        }
    }

    #[test]
    fn a_floor_reads_seconds()
    {
        assert_eq!(
            "0.25".parse::<Floor>(),
            Ok(Floor(Duration::from_millis(250)))
        );
        assert_eq!("1".parse::<Floor>(), Ok(Floor(Duration::from_secs(1))));
        for text in ["-1", "soon"] {
            assert_eq!(
                text.parse::<Floor>(),
                Err(CostError::Seconds { text: text.into() }),
                "{text}"
            );
        }
    }

    #[test]
    fn tests_pair_by_binary_and_name()
    {
        let report = |cases: &[(&str, &str, &str)]| {
            let cases = cases
                .iter()
                .map(|&(binary, test, time)| {
                    format!("<testcase name=\"{test}\" classname=\"{binary}\" time=\"{time}\"/>")
                })
                .collect::<Vec<_>>()
                .concat();
            format!("<testsuites><testsuite>{cases}</testsuite></testsuites>")
        };
        let plain = report(&[
            ("gandr-a", "same::name", "0.100"),
            ("gandr-b", "same::name", "0.200"),
            ("gandr-a", "plain::alone", "0.300"),
            ("gandr-a", "twice", "0.100"),
            ("gandr-a", "tie::b", "0.100"),
            ("gandr-a", "tie::a", "0.100"),
        ]);
        let enforcing = report(&[
            ("gandr-a", "same::name", "0.400"),
            ("gandr-b", "same::name", "0.300"),
            ("gandr-a", "enforcing::alone", "0.500"),
            ("gandr-a", "twice", "0.200"),
            ("gandr-a", "twice", "0.900"),
            ("gandr-a", "tie::b", "0.200"),
            ("gandr-a", "tie::a", "0.200"),
        ]);
        let pairing = pair(
            ReportText::from(plain.as_str()),
            Path::new("plain.xml"),
            ReportText::from(enforcing.as_str()),
            Path::new("enforcing.xml"),
        )
        .unwrap();
        let rows: Vec<(String, String, Factor)> = pairing
            .compared
            .iter()
            .map(|comparison| {
                (
                    comparison.binary.to_string(),
                    comparison.test.to_string(),
                    comparison.factor(),
                )
            })
            .collect();
        let row =
            |binary: &str, test: &str, factor| (binary.to_owned(), test.to_owned(), Factor(factor));
        assert_eq!(rows, vec![
            row("gandr-a", "twice", 900),
            row("gandr-a", "same::name", 400),
            row("gandr-a", "tie::a", 200),
            row("gandr-a", "tie::b", 200),
            row("gandr-b", "same::name", 150),
        ]);
        assert_eq!(pairing.enforcing_only, TestCount(1));
        assert_eq!(pairing.plain_only, TestCount(1));

        let broken = pair(
            ReportText::from(plain.as_str()),
            Path::new("plain.xml"),
            ReportText::from("<testsuites>"),
            Path::new("enforcing.xml"),
        );
        assert!(
            broken.is_err_and(|error| error.to_string().starts_with("enforcing.xml")),
            "a malformed report is refused by its path"
        );
    }

    #[test]
    fn the_report_lists_every_flagged_test_above_the_floor()
    {
        let compared = |test: &str, plain, enforcing| Comparison {
            binary: "gandr-a".into(),
            test: test.into(),
            plain: Duration::from_millis(plain),
            enforcing: Duration::from_millis(enforcing),
        };
        let pairing = Pairing {
            compared: vec![
                compared("short", 1, 200),
                compared("first", 100, 900),
                compared("second", 100, 800),
                compared("third", 100, 700),
                compared("slow", 1_000, 1_500),
            ],
            enforcing_only: TestCount(2),
            plain_only: TestCount(1),
        };
        let baseline = Baseline {
            commit: "5956d6f".parse::<Commit>().unwrap(),
            age: "7".parse::<Hours>().unwrap(),
        };
        let render = |threshold: &str, floor: &str, top: &str| {
            Comparisons {
                pairing: &pairing,
                baseline: &baseline,
                threshold: threshold.parse().unwrap(),
                floor: floor.parse().unwrap(),
                top: top.parse::<RankLimit>().unwrap(),
            }
            .to_string()
        };
        assert_eq!(
            render("4", "0.25", "1"),
            "### Specification cost per test\n\nEach test's time with its specifications enforced \
             over its time without them: this run's enforcing report over the plain baseline of \
             `main` at `5956d6f`, 7 h old. A ratio of 4.00× or more on a test taking at least \
             0.250 s enforcing is flagged.\n\n\
             | Test | Plain | Enforcing | Ratio | |\n\
             | --- | ---: | ---: | ---: | --- |\n\
             | `gandr-a first` | 0.100 s | 0.900 s | 9.00× | flagged |\n\
             | `gandr-a second` | 0.100 s | 0.800 s | 8.00× | flagged |\n\
             | `gandr-a third` | 0.100 s | 0.700 s | 7.00× | flagged |\n\n\
             5 tests in both reports: 1.301 s plain, 4.100 s enforcing, 3.15× overall; 3 \
             flagged. 2 only in the enforcing report, 1 only in the plain baseline.\n",
            "every flagged test despite a limit of one; the short test under the floor is \
             counted but neither listed nor flagged"
        );
        assert_eq!(
            render("8", "0.25", "4"),
            "### Specification cost per test\n\nEach test's time with its specifications enforced \
             over its time without them: this run's enforcing report over the plain baseline of \
             `main` at `5956d6f`, 7 h old. A ratio of 8.00× or more on a test taking at least \
             0.250 s enforcing is flagged.\n\n\
             | Test | Plain | Enforcing | Ratio | |\n\
             | --- | ---: | ---: | ---: | --- |\n\
             | `gandr-a first` | 0.100 s | 0.900 s | 9.00× | flagged |\n\
             | `gandr-a second` | 0.100 s | 0.800 s | 8.00× | flagged |\n\
             | `gandr-a third` | 0.100 s | 0.700 s | 7.00× |  |\n\
             | `gandr-a slow` | 1.000 s | 1.500 s | 1.50× |  |\n\n\
             5 tests in both reports: 1.301 s plain, 4.100 s enforcing, 3.15× overall; 2 \
             flagged. 2 only in the enforcing report, 1 only in the plain baseline.\n",
            "the limit lists unflagged tests after the flagged ones"
        );
        assert!(
            render("4", "2", "4").contains("No test takes 2.000 s or more enforcing.\n\n5 tests"),
            "a floor above every test leaves no table"
        );
    }
}
