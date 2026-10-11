//! Per-test durations read from nextest's JUnit reports, and their summary
//! across runs.
//!
//! nextest writes one `<testcase>` per test with its binary in `classname`,
//! its path inside the binary in `name`, and its wall time in seconds in
//! `time`. A run uploads one report per test lane; a lane is the uploading
//! job, named by the artifact the report arrived in.

extern crate alloc;

use alloc::collections::BTreeMap;
use core::fmt;
use core::time::Duration;
use std::path::Path;

use anodized::spec;
use quenchant_shape::shape::Maybe;

use crate::error::TestCaseDefect;
use crate::error::TimingError;

/// A test's path inside its binary: what nextest's `test()` filter matches.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TestName(String);

/// The test binary a case ran in, as nextest names it in `classname`.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BinaryId(String);

/// The job a report came from, named by the artifact that carried it.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Lane(String);

/// The text of one JUnit report.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct ReportText<'text>(&'text str);

/// Declares `From` conversions and the rendering of a name over `String`.
macro_rules! name {
    ($name:ident) => {
        impl From<&str> for $name
        {
            /// Adopts `name` as given.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(name: &str) -> Self
            {
                Self(name.to_owned())
            }
        }

        impl From<String> for $name
        {
            /// Adopts `name` as given.
            ///
            /// # Specification
            /// trivial.
            #[inline]
            fn from(name: String) -> Self
            {
                Self(name)
            }
        }

        impl fmt::Display for $name
        {
            /// Writes the name as given.
            ///
            /// # Specification
            /// - requires: nothing.
            /// - ensures: writes the carried text unchanged.
            /// - provides: the name the report table and the filter print.
            /// - fails: propagates the formatter's own write failure.
            /// - panics: none.
            /// - executable: none — the formatter exposes no readable output buffer.
            ///
            /// # Adequacy
            /// - hypothesis: L3 — a test name renders exactly as nextest reported it,
            ///   inside the generated filter.
            /// - witness: `priority::tests::overrides_render_one_table_per_level`
            #[inline]
            fn fmt(
                &self,
                f: &mut fmt::Formatter<'_>,
            ) -> fmt::Result
            {
                f.write_str(&self.0)
            }
        }
    };
}

name!(TestName);
name!(BinaryId);
name!(Lane);

impl TestName
{
    /// Whether the name contains `text`, as nextest's `test(TEXT)` matches.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Containment::Contains`] exactly when `text` occurs in the
    ///   name, the empty text included.
    /// - provides: the default `test()` matcher.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a substring, the whole name, and a near miss
    ///   distinguish containment from equality and from a prefix match.
    /// - witness: `priority::tests::a_filter_matches_exactly_or_by_containment`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| (ret == Containment::Contains) == self.0.contains(&text.0))]
    pub fn contains(
        &self,
        text: &Self,
    ) -> Containment
    {
        if self.0.contains(&text.0) {
            Containment::Contains
        }
        else {
            Containment::Lacks
        }
    }
}

/// Whether a test name contains a filter's text.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Containment
{
    /// The text occurs in the name.
    Contains,
    /// It does not.
    Lacks,
}

impl<'text> From<&'text str> for ReportText<'text>
{
    /// Adopts `text` as a report's contents.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(text: &'text str) -> Self
    {
        Self(text)
    }
}

/// One test's wall time in one run of one lane.
///
/// # Specification
/// trivial.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Sample
{
    /// The binary the test ran in.
    pub binary: BinaryId,
    /// The test's path inside the binary.
    pub test: TestName,
    /// Its wall time.
    pub elapsed: Duration,
}

/// Reads every `<testcase>` of one JUnit report.
///
/// # Specification
/// - requires: nothing — any text is admissible input.
/// - ensures: one [`Sample`] per `<testcase>` element, in document order, with
///   its `classname`, its `name`, and its `time` read as seconds.
/// - provides: the durations a [`History`] records.
/// - fails: [`TimingError::Xml`] when `text` is not well-formed XML;
///   [`TimingError::TestCase`] when an element lacks one of the three
///   attributes or its time is not a finite, non-negative number of seconds.
///   `path` names the report in either refusal.
/// - panics: none.
///
/// # Errors
/// - [`TimingError::Xml`] — `text` is not well-formed.
/// - [`TimingError::TestCase`] — a `<testcase>` cannot be read as a timed test.
///
/// # Adequacy
/// - hypothesis: L3 — a two-case report read exactly, then one refusal per
///   missing attribute, a negative time, a non-numeric time and malformed XML;
///   a skipped attribute, a mis-scaled time or a swallowed refusal changes the
///   asserted value or variant.
/// - witness: `report::tests::a_report_reads_every_case_in_order`
/// - witness: `report::tests::an_unreadable_case_is_refused_by_name`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |samples| samples.len() == text.0.matches("<testcase").count()))]
#[inline]
pub fn samples(
    text: ReportText<'_>,
    path: &Path,
) -> Result<Vec<Sample>, TimingError>
{
    let document = roxmltree::Document::parse(text.0).map_err(|error| TimingError::Xml {
        path: path.to_owned(),
        message: error.to_string(),
    })?;
    let refuse = |defect| TimingError::TestCase {
        path: path.to_owned(),
        defect,
    };
    let mut samples = Vec::new();
    for case in document
        .descendants()
        .filter(|node| node.has_tag_name("testcase"))
    {
        let test = case
            .attribute("name")
            .ok_or_else(|| refuse(TestCaseDefect::MissingName))?;
        let binary = case
            .attribute("classname")
            .ok_or_else(|| refuse(TestCaseDefect::MissingBinary))?;
        let time = case
            .attribute("time")
            .ok_or_else(|| refuse(TestCaseDefect::MissingTime))?;
        let elapsed = time
            .parse::<f64>()
            .ok()
            .and_then(|seconds| Duration::try_from_secs_f64(seconds).ok())
            .ok_or_else(|| refuse(TestCaseDefect::Time(time.to_owned())))?;
        samples.push(Sample {
            binary: BinaryId::from(binary),
            test: TestName::from(test),
            elapsed,
        });
    }
    Ok(samples)
}

/// One test's durations across runs, summarised.
///
/// # Specification
/// - provides: the lower median and the extremes of one test's samples in one
///   lane, with the lane and the binary they came from.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Timing
{
    /// The lane whose samples these are.
    pub lane: Lane,
    /// The binary the test ran in.
    pub binary: BinaryId,
    /// The lower median: the sample at position ⌊(n − 1) / 2⌋ in ascending
    /// order, a time some run actually took.
    pub median: Duration,
    /// The fastest sample.
    pub fastest: Duration,
    /// The slowest sample.
    pub slowest: Duration,
    /// How many samples the summary covers.
    pub runs: RunCount,
}

/// A number of runs a summary covers.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct RunCount(usize);

impl From<usize> for RunCount
{
    /// Reads `count` as a number of runs.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(count: usize) -> Self
    {
        Self(count)
    }
}

impl fmt::Display for RunCount
{
    /// Writes the count as a decimal number.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: writes the carried count through `usize`'s rendering.
    /// - provides: the runs column of the report table.
    /// - fails: propagates the formatter's own write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the table row of a three-run test reads `3`.
    /// - witness: `priority::tests::the_table_lists_every_prioritized_test`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        fmt::Display::fmt(&self.0, f)
    }
}

quenchant_shape::reason_enum! {
    /// Why a set of samples has no summary.
    pub mod summary {
        /// The reason a summary is absent.
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        pub enum Absent {
            /// No sample was recorded.
            NoSamples,
        }
    }
}

impl Timing
{
    /// Summarises `samples` of one test in one lane.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: for a non-empty `samples`, the lower median, the minimum, the
    ///   maximum and the count, with `fastest <= median <= slowest`.
    /// - provides: [`summary::Absent::NoSamples`] when `samples` is empty.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — odd and even counts, a single sample and an empty
    ///   set; an upper median, an averaged median or a swapped extreme changes
    ///   the asserted durations.
    /// - witness: `report::tests::the_median_is_a_sample_some_run_took`
    #[inline]
    #[spec(ensures: |ref ret| match *ret {
        Maybe::Present(ref timing) => timing.fastest <= timing.median && timing.median <= timing.slowest
            && timing.runs.0 == samples.len() && samples.contains(&timing.median),
        Maybe::Absent(_) => samples.is_empty(),
    })]
    pub fn of(
        lane: &Lane,
        binary: &BinaryId,
        samples: &[Duration],
    ) -> Maybe<Self, summary::Absent>
    {
        let mut sorted = samples.to_vec();
        sorted.sort_unstable();
        let middle = sorted
            .len()
            .saturating_sub(1)
            .checked_div(2)
            .unwrap_or_default();
        let (Some(&fastest), Some(&median), Some(&slowest)) =
            (sorted.first(), sorted.get(middle), sorted.last())
        else {
            return Maybe::Absent(summary::Absent::NoSamples);
        };
        Maybe::Present(Self {
            lane: lane.clone(),
            binary: binary.clone(),
            median,
            fastest,
            slowest,
            runs: RunCount(sorted.len()),
        })
    }

    /// Whether the samples spread wider than half their median.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Stability::Unsteady`] exactly when `slowest - fastest`
    ///   exceeds half of `median`.
    /// - provides: the flag that asks a reviewer to decide a level by hand.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a spread of exactly half the median is steady and one
    ///   millisecond more is not; an inclusive comparison or a spread measured
    ///   from the median changes the verdict.
    /// - witness: `report::tests::a_spread_past_half_the_median_is_unsteady`
    #[inline]
    #[must_use]
    #[spec(ensures: |ret| (ret == Stability::Unsteady)
        == (self.slowest.saturating_sub(self.fastest).as_nanos().saturating_mul(2) > self.median.as_nanos()))]
    pub fn stability(&self) -> Stability
    {
        let spread = self.slowest.saturating_sub(self.fastest);
        if spread.saturating_add(spread) > self.median {
            Stability::Unsteady
        }
        else {
            Stability::Steady
        }
    }
}

/// Whether a test's samples agree closely enough to place it by its median.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Stability
{
    /// The spread is at most half the median.
    Steady,
    /// The spread exceeds half the median: a reviewer decides.
    Unsteady,
}

/// Durations recorded per test, per binary and per lane.
///
/// # Specification
/// - provides: every recorded sample, grouped so a test's summary in each lane
///   is one lookup.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct History(BTreeMap<TestName, BTreeMap<(BinaryId, Lane), Vec<Duration>>>);

impl History
{
    /// Records `samples` from one report of `lane`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: each sample's duration is appended under its test, binary and
    ///   `lane`; nothing else changes.
    /// - provides: the accumulation one run's reports feed.
    /// - panics: none.
    /// - executable: none — the check would count the whole history, state
    ///   accumulated across calls, so it would cost more than the call.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two runs of two lanes, with one test name in two
    ///   binaries, keep four separate sample lists; merging lanes or binaries
    ///   changes the asserted summaries.
    /// - witness: `report::tests::each_test_is_summarised_by_its_slowest_lane`
    #[inline]
    pub fn record(
        &mut self,
        lane: &Lane,
        samples: Vec<Sample>,
    )
    {
        for sample in samples {
            self.0
                .entry(sample.test)
                .or_default()
                .entry((sample.binary, lane.clone()))
                .or_default()
                .push(sample.elapsed);
        }
    }

    /// Summarises each test by the lane and binary with the greatest median.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one entry per recorded test name, in name order; its
    ///   [`Timing`] is the summary with the greatest median among that name's
    ///   binaries and lanes.
    /// - provides: the time a test's priority is chosen by: the lane it holds
    ///   longest.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a test slow in one lane and fast in another takes the
    ///   slow lane's summary, and a name shared by two binaries takes the
    ///   slower binary's; choosing the first lane, the mean, or the fastest
    ///   changes the asserted summary.
    /// - witness: `report::tests::each_test_is_summarised_by_its_slowest_lane`
    #[inline]
    #[must_use]
    #[spec(ensures: |ref ret| ret.len() == self.0.len() && ret.is_sorted_by(|left, right| left.0 < right.0))]
    pub fn timings(&self) -> Vec<(TestName, Timing)>
    {
        let mut timings = Vec::with_capacity(self.0.len());
        for (test, lanes) in &self.0 {
            let slowest = lanes
                .iter()
                .filter_map(|(key, samples)| {
                    let (ref binary, ref lane) = *key;
                    match Timing::of(lane, binary, samples) {
                        | Maybe::Present(timing) => Some(timing),
                        | Maybe::Absent(summary::Absent::NoSamples) => None,
                    }
                })
                .max_by_key(|timing| timing.median);
            if let Some(timing) = slowest {
                timings.push((test.clone(), timing));
            }
        }
        timings
    }
}

#[cfg(test)]
mod tests
{
    use core::time::Duration;
    use std::path::Path;

    use quenchant_shape::shape::Maybe;

    use super::BinaryId;
    use super::History;
    use super::Lane;
    use super::ReportText;
    use super::RunCount;
    use super::Sample;
    use super::Stability;
    use super::TestName;
    use super::Timing;
    use super::samples;
    use super::summary;
    use crate::error::TestCaseDefect;
    use crate::error::TimingError;

    #[test]
    fn a_report_reads_every_case_in_order()
    {
        let text = "<?xml version=\"1.0\"?><testsuites><testsuite name=\"s\">\
                    <testcase classname=\"gandr-a::tests\" name=\"z::slow\" time=\"174.812\"/>\
                    <testcase classname=\"gandr-b\" name=\"a::fast\" time=\"0.039\"/>\
                    </testsuite></testsuites>";
        let read = samples(ReportText::from(text), Path::new("r.xml"));
        assert_eq!(
            read,
            Ok(vec![
                Sample {
                    binary: BinaryId::from("gandr-a::tests"),
                    test: TestName::from("z::slow"),
                    elapsed: Duration::from_millis(174_812),
                },
                Sample {
                    binary: BinaryId::from("gandr-b"),
                    test: TestName::from("a::fast"),
                    elapsed: Duration::from_millis(39),
                },
            ]),
            "both cases, in document order, timed to the millisecond"
        );
    }

    #[test]
    fn an_unreadable_case_is_refused_by_name()
    {
        let path = Path::new("r.xml");
        let refused = |case: &str| {
            let text = format!("<testsuites><testsuite>{case}</testsuite></testsuites>");
            samples(ReportText::from(text.as_str()), path)
        };
        let defect = |defect| {
            Err(TimingError::TestCase {
                path: path.to_owned(),
                defect,
            })
        };
        assert_eq!(
            refused("<testcase classname=\"b\" time=\"1\"/>"),
            defect(TestCaseDefect::MissingName),
            "no name"
        );
        assert_eq!(
            refused("<testcase name=\"t\" time=\"1\"/>"),
            defect(TestCaseDefect::MissingBinary),
            "no classname"
        );
        assert_eq!(
            refused("<testcase classname=\"b\" name=\"t\"/>"),
            defect(TestCaseDefect::MissingTime),
            "no time"
        );
        assert_eq!(
            refused("<testcase classname=\"b\" name=\"t\" time=\"-1\"/>"),
            defect(TestCaseDefect::Time("-1".into())),
            "a negative time"
        );
        assert_eq!(
            refused("<testcase classname=\"b\" name=\"t\" time=\"soon\"/>"),
            defect(TestCaseDefect::Time("soon".into())),
            "a time that is not a number"
        );
        assert!(
            matches!(
                samples(ReportText::from("<testsuites>"), path),
                Err(TimingError::Xml { ref path, .. }) if path == Path::new("r.xml")
            ),
            "an unclosed element is not XML"
        );
    }

    #[test]
    fn the_median_is_a_sample_some_run_took()
    {
        let lane = Lane::from("junit-cargo-test-enforcing");
        let binary = BinaryId::from("gandr-a");
        let secs = Duration::from_secs;
        let summary = |samples: &[Duration]| Timing::of(&lane, &binary, samples);
        let timing = |median, fastest, slowest, runs| {
            Maybe::Present(Timing {
                lane: lane.clone(),
                binary: binary.clone(),
                median,
                fastest,
                slowest,
                runs: RunCount(runs),
            })
        };
        assert_eq!(
            summary(&[secs(9), secs(1), secs(5)]),
            timing(secs(5), secs(1), secs(9), 3),
            "odd count: the middle sample"
        );
        assert_eq!(
            summary(&[secs(8), secs(2), secs(4), secs(6)]),
            timing(secs(4), secs(2), secs(8), 4),
            "even count: the lower of the two middle samples, not their mean"
        );
        assert_eq!(
            summary(&[secs(3)]),
            timing(secs(3), secs(3), secs(3), 1),
            "one sample"
        );
        assert_eq!(
            summary(&[]),
            Maybe::Absent(summary::Absent::NoSamples),
            "no sample"
        );
    }

    #[test]
    fn a_spread_past_half_the_median_is_unsteady()
    {
        let secs = Duration::from_secs;
        let timing = |slowest| Timing {
            lane: Lane::from("l"),
            binary: BinaryId::from("b"),
            median: secs(10),
            fastest: secs(8),
            slowest,
            runs: RunCount(3),
        };
        assert_eq!(
            timing(secs(13)).stability(),
            Stability::Steady,
            "a spread of half the median"
        );
        assert_eq!(
            timing(secs(13).saturating_add(Duration::from_millis(1))).stability(),
            Stability::Unsteady,
            "a spread one millisecond past half the median"
        );
    }

    #[test]
    fn each_test_is_summarised_by_its_slowest_lane()
    {
        let plain = Lane::from("junit-cargo-test-plain");
        let enforcing = Lane::from("junit-cargo-test-enforcing");
        let secs = Duration::from_secs;
        let sample = |binary: &str, test: &str, seconds| Sample {
            binary: BinaryId::from(binary),
            test: TestName::from(test),
            elapsed: secs(seconds),
        };
        let mut history = History::default();
        for run in [1, 3] {
            history.record(&plain, vec![
                sample("a", "t", run),
                sample("b", "t", 2),
                sample("a", "u", 1),
            ]);
            history.record(&enforcing, vec![
                sample("a", "t", run.saturating_mul(40)),
                sample("b", "t", 90),
            ]);
        }
        let timings = history.timings();
        assert_eq!(
            timings,
            vec![
                (TestName::from("t"), Timing {
                    lane: enforcing,
                    binary: BinaryId::from("b"),
                    median: secs(90),
                    fastest: secs(90),
                    slowest: secs(90),
                    runs: RunCount(2),
                },),
                (TestName::from("u"), Timing {
                    lane: plain,
                    binary: BinaryId::from("a"),
                    median: secs(1),
                    fastest: secs(1),
                    slowest: secs(1),
                    runs: RunCount(2),
                },),
            ],
            "`t` takes its slower binary in its slower lane; `u` has one lane"
        );
    }
}
