//! A commit's `hotpath / <benchmark>` checks as hotpath Cloud writes them: the
//! failed ones, each read into its wall-time line and the sites over its
//! policy's threshold.

use core::fmt;
use core::str::FromStr;

use quenchant_shape::shape::Maybe;
use serde::Deserialize;

use crate::error::GuardError;

/// The prefix of every check hotpath Cloud posts, before the benchmark.
const CHECK_PREFIX: &str = "hotpath / ";

/// The suffix of a summary line naming a site over its policy's threshold.
const FAILS: &str = " · fails the check";

/// The marker opening a site line.
const WARNING: &str = "⚠️ ";

/// The opening of a metric's heading: `**Functions · allocations**`.
const METRIC: &str = "**Functions";

/// The opening of the wall-time line.
const WALL: &str = "Wall time";

/// The opening of a related-metrics row, after which its cells follow.
const RELATED: &str = "| [`";

/// The length of a commit's short form.
const SHORT: usize = 7;

/// A repository on GitHub, `OWNER/NAME`.
///
/// # Specification
/// - provides: the repository whose checks are read and whose issue is filed.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Repository
{
    /// The account owning it.
    owner: String,
    /// Its name within the owner.
    name: String,
}

impl FromStr for Repository
{
    type Err = GuardError;

    /// Reads `OWNER/NAME`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the text, which holds exactly one `/` with a
    ///   non-empty part either side.
    /// - provides: the repository whose checks are read.
    /// - fails: [`GuardError::Repository`] for any other text.
    /// - panics: none.
    /// - executable: none — the outcome is the parse itself.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `OWNER/NAME`, no `/`, two `/` and an empty part;
    ///   accepting any of the last three changes a parse.
    /// - witness: `check::tests::a_repository_is_owner_and_name`
    #[inline]
    fn from_str(text: &str) -> Result<Self, Self::Err>
    {
        match text.split_once('/') {
            Some((owner, name)) if !owner.is_empty() && !name.is_empty() && !name.contains('/') => {
                Ok(Self {
                    owner: owner.to_owned(),
                    name: name.to_owned(),
                })
            },
            _ => Err(GuardError::Repository {
                text: text.to_owned(),
            }),
        }
    }
}

impl fmt::Display for Repository
{
    /// Writes `OWNER/NAME`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the report's commit links name the repository; an
    ///   empty write changes every link.
    /// - witness: `tests::cli::a_failed_check_opens_one_issue_per_function`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "{}/{}", self.owner, self.name)
    }
}

/// A commit, by its full or abbreviated hexadecimal name.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CommitSha(String);

impl FromStr for CommitSha
{
    type Err = GuardError;

    /// Reads seven to forty lowercase hexadecimal digits.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the text.
    /// - provides: the commit whose checks are read.
    /// - fails: [`GuardError::Sha`] for any other text.
    /// - panics: none.
    /// - executable: none — the outcome is the parse itself.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — forty and seven digits, six, forty-one, uppercase and
    ///   a branch name; a length bound off by one or accepting uppercase
    ///   changes a parse.
    /// - witness: `check::tests::a_commit_is_seven_to_forty_hex_digits`
    #[inline]
    fn from_str(text: &str) -> Result<Self, Self::Err>
    {
        let hex = text
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a' ..= b'f').contains(&byte));
        if hex && (SHORT ..= 40).contains(&text.len()) {
            Ok(Self(text.to_owned()))
        }
        else {
            Err(GuardError::Sha {
                text: text.to_owned(),
            })
        }
    }
}

impl CommitSha
{
    /// The commit's first seven digits, for a title.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a forty-digit commit written short; another commit or
    ///   the whole name changes the written form.
    /// - witness: `check::tests::a_commit_is_seven_to_forty_hex_digits`
    #[must_use]
    #[inline]
    pub const fn short(&self) -> ShortSha<'_>
    {
        ShortSha(self)
    }
}

impl fmt::Display for CommitSha
{
    /// Writes the commit as given.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the report links the commit by its full name; an
    ///   empty write changes the link.
    /// - witness: `tests::cli::a_failed_check_opens_one_issue_per_function`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// A commit written by its first seven digits.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct ShortSha<'sha>(&'sha CommitSha);

impl fmt::Display for ShortSha<'_>
{
    /// Writes the commit's first seven digits.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a forty-digit commit written short; an empty write
    ///   changes the written form.
    /// - witness: `check::tests::a_commit_is_seven_to_forty_hex_digits`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(self.0.0.get(.. SHORT).unwrap_or(&self.0.0))
    }
}

/// One check run as the guard's `gh api` query prints it.
#[derive(Debug, Deserialize)]
pub(crate) struct Listed
{
    /// The check's name: `hotpath / gandr` for the `gandr` benchmark.
    name: String,
    /// `queued`, `in_progress` or `completed`.
    status: String,
    /// The outcome of a completed check.
    conclusion: Option<String>,
    /// The check's page.
    html_url: String,
    /// The Markdown summary hotpath Cloud wrote.
    summary: Summary,
}

impl Listed
{
    /// The check read as a concluded hotpath check: a failure, or a pass.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Maybe::Present`] exactly when the name starts with `hotpath
    ///   / `, the status is `completed` and the conclusion is `failure` or
    ///   `success`; a failure carries the name's benchmark, the page and the
    ///   summary read by [`Failure::read`], a pass the benchmark and the page.
    /// - provides: the checks a report is made of; a pending, cancelled or
    ///   foreign check is none of them.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the tests are the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a failed hotpath check, a passing one, a pending one
    ///   and a failed check of another name; reading the pending or foreign one
    ///   as concluded, or the passing one as failed, changes the report.
    /// - witness: `tests::cli::only_a_completed_failed_hotpath_check_is_filed`
    /// - witness: `tests::cli::a_passing_run_marks_its_row_fixed_without_a_comment`
    #[inline]
    pub(crate) fn concluded(self) -> Maybe<Concluded, Unconcluded>
    {
        match (
            self.name.strip_prefix(CHECK_PREFIX),
            self.status.as_str(),
            self.conclusion.as_deref(),
        ) {
            (Some(benchmark), "completed", Some("failure")) => {
                Maybe::Present(Concluded::Failed(Failure::read(
                    Benchmark(benchmark.to_owned()),
                    RunUrl(self.html_url),
                    &self.summary,
                )))
            },
            (Some(benchmark), "completed", Some("success")) => Maybe::Present(Concluded::Passed {
                benchmark: Benchmark(benchmark.to_owned()),
                run: RunUrl(self.html_url),
            }),
            _ => Maybe::Absent(Unconcluded),
        }
    }
}

/// A completed hotpath check: failed, or passed.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Concluded
{
    /// The check failed.
    Failed(Failure),
    /// The check passed.
    Passed
    {
        /// The benchmark the check judged.
        benchmark: Benchmark,
        /// The check's page.
        run: RunUrl,
    },
}

/// Why a listed check is not concluded: it is pending or cancelled, or it is
/// not a hotpath check.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Unconcluded;

/// A benchmark: the part of a check's name after `hotpath / `.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Benchmark(String);

impl FromStr for Benchmark
{
    type Err = core::convert::Infallible;

    /// Reads a benchmark's name as written.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a name read and written back, and an accepted
    ///   verdict's benchmark matched against a failed check's; a lost name
    ///   changes both.
    /// - witness: `check::tests::a_name_reads_back_as_written`
    /// - witness: `tests::cli::an_accepted_landing_settles_its_issue_without_a_comment`
    #[inline]
    fn from_str(text: &str) -> Result<Self, Self::Err>
    {
        Ok(Self(text.to_owned()))
    }
}

impl fmt::Display for Benchmark
{
    /// Writes the benchmark's name.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a name read and written back, and a report's section
    ///   heading; an empty write changes both.
    /// - witness: `check::tests::a_name_reads_back_as_written`
    /// - witness: `tests::cli::a_failed_check_opens_one_issue_per_function`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// A check run's page on GitHub.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RunUrl(String);

impl FromStr for RunUrl
{
    type Err = core::convert::Infallible;

    /// Reads a check's page as written.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an address read and written back; a lost address
    ///   changes it.
    /// - witness: `check::tests::a_name_reads_back_as_written`
    #[inline]
    fn from_str(text: &str) -> Result<Self, Self::Err>
    {
        Ok(Self(text.to_owned()))
    }
}

impl fmt::Display for RunUrl
{
    /// Writes the address.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an address read and written back, and a report's run
    ///   link; an empty write changes both.
    /// - witness: `check::tests::a_name_reads_back_as_written`
    /// - witness: `tests::cli::a_failed_check_opens_one_issue_per_function`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// Why a failure carries no wall-time line: its summary states none.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Unstated;

/// A line of a summary, kept as hotpath Cloud wrote it.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SummaryLine(String);

impl fmt::Display for SummaryLine
{
    /// Writes the line.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a line read and written back, and a report's site
    ///   lines; an empty write changes both.
    /// - witness: `check::tests::a_name_reads_back_as_written`
    /// - witness: `tests::cli::a_failed_check_opens_one_issue_per_function`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// A check's Markdown summary, as hotpath Cloud wrote it.
#[repr(transparent)]
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(transparent)]
pub struct Summary(String);

/// A function or bench over its policy's threshold, by its profiled name.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct SiteName(String);

impl FromStr for SiteName
{
    type Err = core::convert::Infallible;

    /// Reads a profiled name as written.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a name read and written back, and an issue's title
    ///   read back to its function; a lost name changes both.
    /// - witness: `check::tests::a_name_reads_back_as_written`
    /// - witness: `tests::cli::a_second_pull_request_adds_a_row_and_a_comment`
    #[inline]
    fn from_str(text: &str) -> Result<Self, Self::Err>
    {
        Ok(Self(text.to_owned()))
    }
}

impl SiteName
{
    /// The name a title carries: its last two path segments, or the whole
    /// name when it has fewer.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `gandr_core_checker::module::decide` is `module::decide`;
    ///   `closure check` stays `closure check`.
    /// - provides: a title short enough to read in a list.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the split is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a three-segment path, a two-segment one and a bench
    ///   name; keeping one segment or the whole path changes the title.
    /// - witness: `check::tests::a_site_is_titled_by_its_last_two_segments`
    #[must_use]
    #[inline]
    pub fn short(&self) -> Self
    {
        let mut ends = self.0.rmatch_indices("::").map(|(index, _)| index);
        let short = match (ends.next(), ends.next()) {
            (Some(_), Some(start)) => self.0.get(start.saturating_add(2) ..).unwrap_or(&self.0),
            _ => &self.0,
        };
        Self(short.to_owned())
    }
}

impl fmt::Display for SiteName
{
    /// Writes the name.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a name read and written back, and an issue's title;
    ///   an empty write changes both.
    /// - witness: `check::tests::a_name_reads_back_as_written`
    /// - witness: `tests::cli::a_failed_check_opens_one_issue_per_function`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// A site over its policy's threshold.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Site
{
    /// Its profiled name.
    pub name: SiteName,
    /// The crate its source lives in, read from its link.
    pub krate: Maybe<CrateDir, Unstated>,
    /// Its link and before/after numbers, as the summary wrote them without
    /// the warning marker and the verdict.
    pub line: SummaryLine,
}

/// A crate's directory under `crates/`.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct CrateDir(String);

impl fmt::Display for CrateDir
{
    /// Writes the directory's name.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an issue's body names the function's crate; an empty
    ///   write changes the body.
    /// - witness: `tests::cli::a_failed_check_opens_one_issue_per_function`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0)
    }
}

impl CrateDir
{
    /// The area label of the crate's tier: `core-checker` is `area:core`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `area:` and the directory's first `-`-separated part when it
    ///   is one of the tiers `kernel`, `theory`, `core`, `storage`, `runtime`,
    ///   `surface` or `workflow`; absent otherwise.
    /// - provides: the area a regression is labelled with, from where it shows.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the tier table is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a core, a surface and an unknown prefix; the whole
    ///   directory as the label, or a label for an unknown tier, changes the
    ///   issue's labels.
    /// - witness: `check::tests::a_crate_names_its_tier`
    #[inline]
    pub fn area(&self) -> Maybe<AreaLabel, Unstated>
    {
        let tier = self.0.split('-').next().unwrap_or_default();
        if [
            "kernel", "theory", "core", "storage", "runtime", "surface", "workflow",
        ]
        .contains(&tier)
        {
            Maybe::Present(AreaLabel(format!("area:{tier}")))
        }
        else {
            Maybe::Absent(Unstated)
        }
    }
}

/// A repository label naming an area: `area:core`.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct AreaLabel(String);

impl FromStr for AreaLabel
{
    type Err = Unstated;

    /// Reads a label that names an area: one starting `area:`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: on success the text, which starts `area:`.
    /// - provides: a pull request's area labels, the others left out.
    /// - fails: [`Unstated`] for a label of another kind.
    /// - panics: none.
    /// - executable: none — the outcome is the parse itself.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a regressed pull request's `area:theory` beside
    ///   `kind:feature`; keeping the kind or losing the area changes the
    ///   issue's labels.
    /// - witness: `tests::cli::a_failed_check_opens_one_issue_per_function`
    #[inline]
    fn from_str(text: &str) -> Result<Self, Self::Err>
    {
        if text.starts_with("area:") {
            Ok(Self(text.to_owned()))
        }
        else {
            Err(Unstated)
        }
    }
}

impl fmt::Display for AreaLabel
{
    /// Writes the label.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — an opened issue carries its area label; an empty
    ///   write changes the label.
    /// - witness: `tests::cli::a_failed_check_opens_one_issue_per_function`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0)
    }
}

/// One metric's sites over threshold: allocations or timing.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Section
{
    /// The heading hotpath Cloud wrote: `Functions · allocations`.
    pub metric: SummaryLine,
    /// Its sites, in the summary's order.
    pub sites: Vec<Site>,
}

/// Whether a related-metrics row's call count moved.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Calls
{
    /// Every row's calls read the same before and after.
    Unchanged,
    /// Some row's calls changed.
    Changed,
}

/// A percentage change, in tenths of a point: `+3.2%` is 32.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Percent(i64);

impl fmt::Display for Percent
{
    /// Writes the change signed, with its tenth when it has one: `+31`,
    /// `+3.2`, `-5`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a decimal rise, a whole fall and no change; a sign
    ///   chosen at another bound, or an empty write, changes one of them.
    /// - witness: `check::tests::a_uniform_timing_shift_is_a_runner_shift`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let sign = if self.0 < 0 { "-" } else { "+" };
        let whole = self.0.unsigned_abs().div_euclid(10);
        match self.0.unsigned_abs().rem_euclid(10) {
            0 => write!(f, "{sign}{whole}"),
            tenth => write!(f, "{sign}{whole}.{tenth}"),
        }
    }
}

impl FromStr for SummaryLine
{
    type Err = core::convert::Infallible;

    /// Reads a line as written.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a line read and written back; a lost line changes it.
    /// - witness: `check::tests::a_name_reads_back_as_written`
    #[inline]
    fn from_str(text: &str) -> Result<Self, Self::Err>
    {
        Ok(Self(text.to_owned()))
    }
}

impl SummaryLine
{
    /// A section heading's metric: `Functions · timing` is `timing`.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the line after `Functions · `, or the whole line without it.
    /// - provides: an index row's metric.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the strip is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the allocations and timing headings; keeping the
    ///   prefix changes the row.
    /// - witness: `tests::cli::a_failed_check_opens_one_issue_per_function`
    #[must_use]
    #[inline]
    pub fn metric(&self) -> Self
    {
        Self(
            self.0
                .strip_prefix("Functions · ")
                .unwrap_or(&self.0)
                .to_owned(),
        )
    }

    /// A site line's numbers: the line after its link's `): `.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the line after its first `): `, or the whole line without
    ///   one.
    /// - provides: an index row's delta.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the split is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a site line with its link; keeping the link changes
    ///   the row.
    /// - witness: `tests::cli::a_failed_check_opens_one_issue_per_function`
    #[must_use]
    #[inline]
    pub fn delta(&self) -> Self
    {
        Self(
            self.0
                .split_once("): ")
                .map_or(self.0.as_str(), |(_, delta)| delta)
                .to_owned(),
        )
    }

    /// The line's first bold percentage: `**+31%**` is +31.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the first `**…%**` span whose inside reads as an optionally
    ///   signed number with at most one decimal, in tenths of a point; absent
    ///   when none does.
    /// - provides: the delta a runner shift compares.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the scan is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a site's `avg` delta beside its `total` one, a wall
    ///   line, a decimal change, a doubled sign, a second decimal and a line
    ///   without one; reading the second delta, dropping the decimal or the
    ///   sign, or reading a malformed span changes the shift.
    /// - witness: `check::tests::a_uniform_timing_shift_is_a_runner_shift`
    /// - witness: `check::tests::a_delta_is_one_signed_number_of_at_most_one_decimal`
    #[inline]
    pub fn percent(&self) -> Maybe<Percent, Unstated>
    {
        for (start, _) in self.0.match_indices("**") {
            let Some((number, _)) = self
                .0
                .get(start.saturating_add(2) ..)
                .and_then(|rest| rest.split_once("%**"))
            else {
                continue;
            };
            let (negative, digits) = number.strip_prefix('-').map_or_else(
                || (false, number.strip_prefix('+').unwrap_or(number)),
                |digits| (true, digits),
            );
            let (whole, tenth) = digits.split_once('.').unwrap_or((digits, "0"));
            let decimal =
                |text: &str| !text.is_empty() && text.bytes().all(|byte| byte.is_ascii_digit());
            if !decimal(whole) || !decimal(tenth) || tenth.len() > 1 {
                continue;
            }
            let (Ok(whole), Ok(tenth)) = (whole.parse::<i64>(), tenth.parse::<i64>())
            else {
                continue;
            };
            let tenths = whole.saturating_mul(10).saturating_add(tenth);
            return Maybe::Present(Percent(if negative {
                tenths.saturating_neg()
            }
            else {
                tenths
            }));
        }
        Maybe::Absent(Unstated)
    }
}

/// Why a failure is no runner shift: it measures allocations, a call count
/// moved, the commit's allocations failed too, or its deltas differ.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Unshifted;

/// How far a runner shift moved the wall time and every regressed function:
/// from `low` to `high`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Shift
{
    /// The smallest delta.
    pub low: Percent,
    /// The largest delta.
    pub high: Percent,
}

/// The widest spread of deltas a runner shift admits, in tenths of a point:
/// in the shift that motivated it, every function moved +25 to +31 % together.
const SHIFT_BAND: i64 = 80;

/// A failed hotpath check, read from its summary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Failure
{
    /// The benchmark the check judged.
    pub benchmark: Benchmark,
    /// The check's page.
    pub run: RunUrl,
    /// The summary's wall-time line: `` Wall time `401.60 ms → 510.60 ms`
    /// **+27%** ``.
    pub wall: Maybe<SummaryLine, Unstated>,
    /// Each metric's sites over threshold.
    pub sections: Vec<Section>,
    /// Whether a related-metrics row's calls moved.
    pub calls: Calls,
}

impl Failure
{
    /// Reads a failed check's summary.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the wall-time line is the first line starting `Wall time`;
    ///   each line starting `**Functions` opens a section under that heading
    ///   without its asterisks; each line starting with the warning marker and
    ///   ending `· fails the check` is a site of the open section, or of a
    ///   section headed `Functions` when none is open, named by its first
    ///   backquoted link text and placed in the crate its link's `crates/`
    ///   component names; the calls are changed when a related-metrics row's
    ///   second cell carries a percentage or differs either side of `→`. Every
    ///   other line is ignored, so a summary of another shape reads as a
    ///   failure without sites.
    /// - provides: the sites and numbers the issue states.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause would read the summary again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the summary of a real failed `gandr` check: five
    ///   sites under allocations, the wall line, and the related-metrics tables
    ///   after them; a table row read as a site, a lost heading, a wrong crate
    ///   or a moved call count read as unchanged changes the reading.
    /// - witness: `check::tests::a_summary_reads_into_its_sites`
    /// - witness: `check::tests::a_uniform_timing_shift_is_a_runner_shift`
    /// - witness: `check::tests::a_summary_of_another_shape_reads_without_sites`
    #[must_use]
    #[inline]
    pub fn read(
        benchmark: Benchmark,
        run: RunUrl,
        summary: &Summary,
    ) -> Self
    {
        let mut wall = Maybe::Absent(Unstated);
        let mut sections: Vec<Section> = Vec::new();
        let mut calls = Calls::Unchanged;
        for line in summary.0.lines().map(str::trim_end) {
            if line.starts_with(WALL) && matches!(wall, Maybe::Absent(_)) {
                wall = Maybe::Present(SummaryLine(line.to_owned()));
            }
            else if line.starts_with(METRIC) {
                sections.push(Section {
                    metric: SummaryLine(line.trim_matches('*').to_owned()),
                    sites: Vec::new(),
                });
            }
            else if let Some(row) = line.strip_prefix(RELATED) {
                let moved = row.split('|').nth(1).map(str::trim).is_some_and(|cell| {
                    cell.contains('%')
                        || cell
                            .split_once(" → ")
                            .is_some_and(|(before, after)| before != after)
                });
                if moved {
                    calls = Calls::Changed;
                }
            }
            else if let Some(body) = line
                .strip_prefix(WARNING)
                .and_then(|rest| rest.strip_suffix(FAILS))
            {
                let between = |open: &str, close: &str| {
                    body.split_once(open)
                        .and_then(|(_, rest)| rest.split_once(close))
                        .map(|(inner, _)| inner)
                };
                let site = Site {
                    name: SiteName(between("[`", "`]").unwrap_or(body).to_owned()),
                    krate: between("/crates/", "/").map_or(Maybe::Absent(Unstated), |dir| {
                        Maybe::Present(CrateDir(dir.to_owned()))
                    }),
                    line: SummaryLine(body.to_owned()),
                };
                match sections.last_mut() {
                    Some(section) => section.sites.push(site),
                    None => sections.push(Section {
                        metric: SummaryLine("Functions".to_owned()),
                        sites: vec![site],
                    }),
                }
            }
        }
        Self {
            benchmark,
            run,
            wall,
            sections,
            calls,
        }
    }

    /// Whether the failure is a runner shift: the wall time and every
    /// regressed function slower by about the same ratio, as a slower runner
    /// makes them, rather than a change to the code.
    ///
    /// # Specification
    /// - requires: `commit` holds every failed check of the failure's commit.
    /// - ensures: [`Maybe::Present`] exactly when the failure has sites, each
    ///   of its sections and of every failure in `commit` measures timing (its
    ///   heading ends `timing`, so the allocation report is clean), no
    ///   related-metrics row's calls moved, and the wall line's delta and each
    ///   site's first delta are all stated, all positive and within 8 points of
    ///   each other; the shift carries the smallest and the largest.
    /// - provides: the `runner shift` row, filed without a comment.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the conjunction is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a real shift's timing failure (wall +28, `decide`
    ///   +31), the same beside a failed allocation check, with a moved call
    ///   count, and a real regression (wall +27, `decide` +45); reading any of
    ///   the last three as a shift, or the first as none, changes the row.
    /// - witness: `check::tests::a_uniform_timing_shift_is_a_runner_shift`
    #[inline]
    pub fn shift(
        &self,
        commit: &[Self],
    ) -> Maybe<Shift, Unshifted>
    {
        let timing = |failure: &Self| {
            failure
                .sections
                .iter()
                .all(|section| section.metric.0.ends_with("timing"))
        };
        let sites = self
            .sections
            .iter()
            .flat_map(|section| section.sites.iter());
        if sites.clone().next().is_none()
            || !commit.iter().chain(core::iter::once(self)).all(timing)
            || self.calls == Calls::Changed
        {
            return Maybe::Absent(Unshifted);
        }
        let Maybe::Present(ref wall) = self.wall
        else {
            return Maybe::Absent(Unshifted);
        };
        let mut deltas = Vec::new();
        for line in core::iter::once(wall).chain(sites.map(|site| &site.line)) {
            match line.percent() {
                Maybe::Present(delta) => deltas.push(delta),
                Maybe::Absent(_) => return Maybe::Absent(Unshifted),
            }
        }
        match (deltas.iter().min(), deltas.iter().max()) {
            (Some(&low), Some(&high))
                if low.0 > 0 && high.0.saturating_sub(low.0) <= SHIFT_BAND =>
            {
                Maybe::Present(Shift { low, high })
            },
            _ => Maybe::Absent(Unshifted),
        }
    }
}

#[cfg(test)]
mod tests
{
    use quenchant_shape::shape::Maybe;

    use super::AreaLabel;
    use super::Benchmark;
    use super::Calls;
    use super::CommitSha;
    use super::CrateDir;
    use super::Failure;
    use super::Percent;
    use super::Repository;
    use super::RunUrl;
    use super::Shift;
    use super::SiteName;
    use super::Summary;
    use super::SummaryLine;
    use super::Unshifted;

    /// The summary of a real failed `gandr` check, trimmed to two sites and
    /// one related-metrics table.
    const SUMMARY: &str = "<!-- hotpath:benchmark=gandr -->
### `gandr` · ⚠️ 2 regressions

[`76dd52f`](https://github.com/gandr-lang/gandr/commit/76dd52f) (`theory-model-record`) vs [`71dc603`](https://github.com/gandr-lang/gandr/commit/71dc603)
Wall time `401.60 ms → 510.60 ms` **+27%**

**Functions · allocations**
⚠️ [`gandr_core_checker::module::decide`](https://github.com/gandr-lang/gandr/blob/76dd52f/crates/core-checker/src/module.rs#L1009): avg `1444 → 2558` **+77%**, total `452181 → 813738` **+80%** · fails the check
⚠️ [`lsp keystroke`](https://github.com/gandr-lang/gandr/blob/76dd52f/crates/surface-driver/benches/hotpath.rs#L177): avg `59331 → 61258` **+3.2%**, total **+3.2%** · fails the check

**Related metrics**

| Allocations | Calls | Avg |
|:--|--:|--:|
| [`gandr_core_checker::module::decide`](https://github.com/gandr-lang/gandr/blob/76dd52f/crates/core-checker/src/module.rs#L1009) | 313 → 318 +1.6% | 1444 → 2558 +77% |
";

    #[test]
    fn a_summary_reads_into_its_sites()
    {
        let failure = Failure::read(
            Benchmark("gandr".into()),
            RunUrl("https://github.com/gandr-lang/gandr/runs/1".into()),
            &Summary(SUMMARY.to_owned()),
        );
        assert_eq!(
            failure.wall,
            Maybe::Present(SummaryLine(
                "Wall time `401.60 ms → 510.60 ms` **+27%**".into()
            ))
        );
        let [ref section] = *failure.sections.as_slice()
        else {
            panic!("one section: {:?}", failure.sections);
        };
        assert_eq!(
            section.metric,
            SummaryLine("Functions · allocations".into())
        );
        let names = section
            .sites
            .iter()
            .map(|site| (site.name.0.as_str(), site.krate.clone()))
            .collect::<Vec<_>>();
        assert_eq!(names, [
            (
                "gandr_core_checker::module::decide",
                Maybe::Present(CrateDir("core-checker".into()))
            ),
            (
                "lsp keystroke",
                Maybe::Present(CrateDir("surface-driver".into()))
            ),
        ]);
        assert_eq!(
            section.sites.first().map(|site| site.line.0.as_str()),
            Some(
                "[`gandr_core_checker::module::decide`](https://github.com/gandr-lang/gandr/blob/76dd52f/crates/core-checker/src/module.rs#L1009): avg `1444 → 2558` **+77%**, total `452181 → 813738` **+80%**"
            )
        );
        assert_eq!(failure.calls, Calls::Changed, "313 → 318 moved");
    }

    /// A runner shift's failed `gandr-timing` check: the wall time +28 %,
    /// `decide` +31 %, its calls unchanged.
    const SHIFTED: &str = "### `gandr-timing` · ⚠️ 1 regression
Wall time `313.23 ms → 401.90 ms` **+28%**

**Functions · timing**
⚠️ [`gandr_core_checker::module::decide`](https://github.com/gandr-lang/gandr/blob/e6f58bf/crates/core-checker/src/module.rs#L1009): avg `179.28 µs → 235.30 µs` **+31%** · fails the check

| Timing | Calls | Avg | P95 | Total | % Total |
|:--|--:|--:|--:|--:|--:|
| [`gandr_core_checker::module::decide`](https://github.com/gandr-lang/gandr/blob/e6f58bf/crates/core-checker/src/module.rs#L1009) | 319 → 319 | 179.28 µs → 235.30 µs +31% | 1.06 ms → 1.38 ms +31% | 57.19 ms → 75.06 ms +31% | 18.3% → 18.7% |
";

    #[test]
    fn a_uniform_timing_shift_is_a_runner_shift()
    {
        let read = |benchmark: &str, summary: &str| {
            Failure::read(
                Benchmark(benchmark.into()),
                RunUrl("https://github.com/gandr-lang/gandr/runs/1".into()),
                &Summary(summary.to_owned()),
            )
        };
        let shifted = read("gandr-timing", SHIFTED);
        assert_eq!(
            shifted.shift(&[]),
            Maybe::Present(Shift {
                low: Percent(280),
                high: Percent(310),
            })
        );
        assert_eq!(
            shifted.shift(&[read("gandr", SUMMARY)]),
            Maybe::Absent(Unshifted),
            "the commit's allocations failed too"
        );
        let moved = read(
            "gandr-timing",
            &SHIFTED.replace("319 → 319", "319 → 325 +1.9%"),
        );
        assert_eq!(
            moved.shift(&[]),
            Maybe::Absent(Unshifted),
            "a call count moved"
        );
        let unmarked = read("gandr-timing", &SHIFTED.replace("319 → 319", "319 → 325"));
        assert_eq!(
            unmarked.shift(&[]),
            Maybe::Absent(Unshifted),
            "a call count moved, its cell without a percentage"
        );
        let real = read("gandr-timing", &SHIFTED.replace("**+31%**", "**+45%**"));
        assert_eq!(real.shift(&[]), Maybe::Absent(Unshifted), "+28 against +45");
        let flat = read(
            "gandr-timing",
            &SHIFTED
                .replace("**+28%**", "**+0%**")
                .replace("**+31%**", "**+0.5%**"),
        );
        assert_eq!(
            flat.shift(&[]),
            Maybe::Absent(Unshifted),
            "a shift is a slowdown: a flat wall time is none"
        );
        let decimal = read("gandr-timing", &SHIFTED.replace("**+31%**", "**+30.5%**"));
        assert_eq!(
            decimal.shift(&[]),
            Maybe::Present(Shift {
                low: Percent(280),
                high: Percent(305),
            })
        );
        assert_eq!(Percent(305).to_string(), "+30.5");
        assert_eq!(Percent(-50).to_string(), "-5");
        assert_eq!(
            Percent(0).to_string(),
            "+0",
            "no change is written as a rise"
        );
    }

    #[test]
    fn a_delta_is_one_signed_number_of_at_most_one_decimal()
    {
        let percent = |line: &str| SummaryLine(line.into()).percent();
        assert_eq!(
            percent("avg `1 → 2` **+31%**"),
            Maybe::Present(Percent(310))
        );
        assert_eq!(percent("**-2.5%**"), Maybe::Present(Percent(-25)));
        assert_eq!(
            percent("avg **+-5%**, total **3.25%**, wall **+4.0%**"),
            Maybe::Present(Percent(40)),
            "a doubled sign and a second decimal are not deltas"
        );
        assert_eq!(
            percent("**Functions · %** and **.5%**"),
            Maybe::Absent(super::Unstated)
        );
    }

    #[test]
    fn a_summary_of_another_shape_reads_without_sites()
    {
        let failure = Failure::read(
            Benchmark("store".into()),
            RunUrl("https://github.com/gandr-lang/gandr/runs/2".into()),
            &Summary("### `store` · failed to upload".to_owned()),
        );
        assert_eq!(failure.sections, []);
        assert!(matches!(failure.wall, Maybe::Absent(_)));
    }

    #[test]
    fn a_name_reads_back_as_written()
    {
        let name = "gandr_core_checker::module::decide";
        let Ok(benchmark) = name.parse::<Benchmark>();
        assert_eq!(benchmark.to_string(), name);
        let Ok(site) = name.parse::<SiteName>();
        assert_eq!(site.to_string(), name);
        let address = "https://github.com/gandr-lang/gandr/runs/1";
        let Ok(run) = address.parse::<RunUrl>();
        assert_eq!(run.to_string(), address);
        let line = "avg `1444 → 2558` **+77%**";
        let Ok(summary) = line.parse::<SummaryLine>();
        assert_eq!(summary.to_string(), line);
        let Ok(subject) = "#1358".parse::<crate::report::Subject>();
        assert_eq!(subject.to_string(), "#1358");
    }

    #[test]
    fn a_site_is_titled_by_its_last_two_segments()
    {
        let short = |name: &str| SiteName(name.into()).short().to_string();
        assert_eq!(
            short("gandr_core_checker::module::decide"),
            "module::decide"
        );
        assert_eq!(short("recheck::recheck"), "recheck::recheck");
        assert_eq!(short("closure check"), "closure check");
    }

    #[test]
    fn a_crate_names_its_tier()
    {
        let area = |dir: &str| CrateDir(dir.into()).area();
        assert_eq!(
            area("core-checker"),
            Maybe::Present(AreaLabel("area:core".into()))
        );
        assert_eq!(
            area("surface-driver"),
            Maybe::Present(AreaLabel("area:surface".into()))
        );
        assert!(matches!(area("quenchant-shape"), Maybe::Absent(_)));
    }

    #[test]
    fn a_repository_is_owner_and_name()
    {
        assert!("gandr-lang/gandr".parse::<Repository>().is_ok());
        for text in ["gandr", "a/b/c", "/gandr", "gandr-lang/"] {
            assert!(text.parse::<Repository>().is_err(), "{text}");
        }
    }

    #[test]
    fn a_commit_is_seven_to_forty_hex_digits()
    {
        for text in ["914a768fb32501be92e5cb4d28ce6613dfa01022", "914a768"] {
            assert!(text.parse::<CommitSha>().is_ok(), "{text}");
        }
        for text in [
            "914a76",
            "914a768fb32501be92e5cb4d28ce6613dfa010220",
            "914A768",
            "main",
        ] {
            assert!(text.parse::<CommitSha>().is_err(), "{text}");
        }
        let sha: CommitSha = "914a768fb32501be92e5cb4d28ce6613dfa01022".parse().unwrap();
        assert_eq!(sha.short().to_string(), "914a768");
    }
}
