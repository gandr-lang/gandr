//! A commit's `hotpath / <benchmark>` checks as hotpath Cloud writes them.
//!
//! A failed one is read into its wall-time line, its base commit and the
//! sites over its policy's threshold, and each section is judged against the
//! run's global shift ([`crate::judge::shift`]).

use core::fmt;
use core::str::FromStr;

use quenchant_shape::shape::Maybe;
use serde::Deserialize;

use crate::error::GuardError;
use crate::judge::shift::Crossing;
use crate::judge::shift::GlobalShift;
use crate::judge::shift::Reading;
use crate::judge::shift::Unread;

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

/// The marker before the base commit's link on a summary's comparison line:
/// `` [`head`](…) vs [`base`](…/commit/<sha>) ``.
const VERSUS: &str = " vs [`";

/// The path component before a commit's name in its link.
const COMMIT: &str = "/commit/";

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
    /// - witness: `tests::cli::a_passing_run_edits_its_comment_and_marks_its_row_fixed`
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

/// What a section of a failed check measures.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Measure
{
    /// Wall-clock time: its heading ends `timing`.
    Timing,
    /// Allocations, or a heading of another shape.
    Other,
}

/// How a failed check's section files its sites.
#[derive(Clone, Copy, Debug)]
pub enum Judgement<'reading>
{
    /// The check's own judgement, every site filed as a regression: an
    /// allocation section, or a timing one whose run read no global shift.
    Unread,
    /// The runner's: no site moved past the threshold beside the global
    /// shift, while the wall time and the shift both did. Every site files as
    /// the shift.
    Shifted(GlobalShift),
    /// Each site regresses when its move beside the global shift crosses the
    /// threshold, and is not filed otherwise.
    Relative(&'reading Reading),
}

/// What one site of a failed check files as.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Filing
{
    /// A regression: its row is `open`.
    Regressed,
    /// The runner's: its row is `runner shift`.
    Shifted(GlobalShift),
    /// Within the threshold beside the global shift: no row.
    Within,
}

impl Section
{
    /// What the section measures, by its heading.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Section::judged`].
    /// - witness: `check::tests::a_uniform_timing_shift_is_a_runner_shift`
    #[must_use]
    #[inline]
    pub fn measure(&self) -> Measure
    {
        if self.metric.0.ends_with("timing") {
            Measure::Timing
        }
        else {
            Measure::Other
        }
    }

    /// How this section files its sites, given its run's reading.
    ///
    /// # Specification
    /// - requires: `reading` is the global shift read for the section's check.
    /// - ensures: [`Judgement::Unread`] for a section whose heading does not
    ///   end `timing` or a reading that is absent; [`Judgement::Shifted`] when
    ///   no site crosses the threshold beside the shift ([`Reading::site`]) and
    ///   the wall time and the shift both cross it ([`Reading::runner`]);
    ///   [`Judgement::Relative`] otherwise.
    /// - provides: the judgement each site's row follows. Timing and
    ///   allocations are judged apart: another check's allocation failure
    ///   leaves a timing shift the runner's.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the cases are the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the replayed run's timing section (three sites beside
    ///   a +27 % shift, wall +28 %), one function at +40 % among functions at
    ///   +2 %, a section of functions at +2 % with a site at +8 %, an
    ///   allocation section beside a reading, and a timing section without one;
    ///   a shift read with a site past the threshold, a +2 % runner read as a
    ///   shift, or an allocation section judged relative changes the filing.
    /// - witness: `check::tests::a_uniform_timing_shift_is_a_runner_shift`
    /// - witness: `tests::cli::a_runner_shift_is_read_over_every_function`
    #[must_use]
    #[inline]
    pub fn judged<'reading>(
        &self,
        reading: Maybe<&'reading Reading, Unread>,
    ) -> Judgement<'reading>
    {
        let Maybe::Present(reading) = reading
        else {
            return Judgement::Unread;
        };
        if self.measure() == Measure::Other {
            return Judgement::Unread;
        }
        let crossed = self
            .sites
            .iter()
            .any(|site| reading.site(&site.name) == Crossing::Crosses);
        match (crossed, reading.runner()) {
            (false, Crossing::Crosses) => Judgement::Shifted(reading.shift()),
            (true, Crossing::Crosses | Crossing::Within) | (false, Crossing::Within) => {
                Judgement::Relative(reading)
            },
        }
    }
}

impl Judgement<'_>
{
    /// What `site` files as under this judgement.
    ///
    /// # Specification
    /// - requires: `site` is a site of the judged section.
    /// - ensures: [`Filing::Regressed`] under [`Judgement::Unread`];
    ///   [`Filing::Shifted`] under [`Judgement::Shifted`]; under
    ///   [`Judgement::Relative`], [`Filing::Regressed`] when the site crosses
    ///   the threshold beside the shift and [`Filing::Within`] otherwise.
    /// - provides: one site's row, or none.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the cases are the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`Section::judged`].
    /// - witness: `check::tests::a_uniform_timing_shift_is_a_runner_shift`
    #[must_use]
    #[inline]
    pub fn filing(
        &self,
        site: &Site,
    ) -> Filing
    {
        match *self {
            Self::Unread => Filing::Regressed,
            Self::Shifted(shift) => Filing::Shifted(shift),
            Self::Relative(reading) => match reading.site(&site.name) {
                Crossing::Crosses => Filing::Regressed,
                Crossing::Within => Filing::Within,
            },
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
}

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
    /// The commit the check compared the head with, from the summary's
    /// comparison line.
    pub base: Maybe<CommitSha, Unstated>,
    /// Each metric's sites over threshold.
    pub sections: Vec<Section>,
}

impl Failure
{
    /// Reads a failed check's summary.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the wall-time line is the first line starting `Wall time`;
    ///   the base is the commit the first link after ``vs [` `` names by its
    ///   `/commit/` path, when that reads as a commit; each line starting
    ///   `**Functions` opens a section under that heading without its
    ///   asterisks; each line starting with the warning marker and ending `·
    ///   fails the check` is a site of the open section, or of a section headed
    ///   `Functions` when none is open, named by its first backquoted link text
    ///   and placed in the crate its link's `crates/` component names. Every
    ///   other line is ignored, so a summary of another shape reads as a
    ///   failure without sites.
    /// - provides: the sites and numbers the issue states, and the base whose
    ///   report the global shift is read against.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the clause would read the summary again.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the summary of a real failed `gandr` check: five
    ///   sites under allocations, the comparison line, the wall line, and the
    ///   related-metrics tables after them; a table row read as a site, a lost
    ///   heading, a wrong crate or the head read as the base changes the
    ///   reading.
    /// - witness: `check::tests::a_summary_reads_into_its_sites`
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
        let mut base = Maybe::Absent(Unstated);
        let mut sections: Vec<Section> = Vec::new();
        for line in summary.0.lines().map(str::trim_end) {
            if line.starts_with(WALL) && matches!(wall, Maybe::Absent(_)) {
                wall = Maybe::Present(SummaryLine(line.to_owned()));
            }
            else if let Some(link) = line
                .split_once(VERSUS)
                .filter(|_| matches!(base, Maybe::Absent(_)))
                .and_then(|(_, rest)| rest.split_once(COMMIT))
                .and_then(|(_, rest)| rest.split_once(')'))
            {
                if let Ok(sha) = link.0.parse::<CommitSha>() {
                    base = Maybe::Present(sha);
                }
            }
            else if line.starts_with(METRIC) {
                sections.push(Section {
                    metric: SummaryLine(line.trim_matches('*').to_owned()),
                    sites: Vec::new(),
                });
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
            base,
            sections,
        }
    }
}

#[cfg(test)]
mod tests
{
    use quenchant_shape::shape::Maybe;

    use super::AreaLabel;
    use super::Benchmark;
    use super::CommitSha;
    use super::CrateDir;
    use super::Failure;
    use super::Filing;
    use super::Judgement;
    use super::Repository;
    use super::RunUrl;
    use super::Section;
    use super::SiteName;
    use super::Summary;
    use super::SummaryLine;
    use crate::judge::Input;
    use crate::judge::Policy;
    use crate::judge::Run;
    use crate::judge::shift::Reading;
    use crate::judge::shift::Unread;

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
        assert_eq!(
            failure.base,
            Maybe::Present("71dc603".parse::<CommitSha>().unwrap()),
            "the base is the commit after `vs`, not the head"
        );
    }

    /// `73f2e46`'s failed `gandr-timing` check, its related metrics dropped:
    /// the wall time +28 % and three functions +23 to +32 % against
    /// `ac58445`.
    const REPLAYED: &str = "### `gandr-timing` · ⚠️ 3 regressions

[`def8465`](https://github.com/gandr-lang/gandr/commit/def8465ee289cd7d95d3e79cdee0d64ff0c20ae7) (`theory-1886-native-j`) vs [`ac58445`](https://github.com/gandr-lang/gandr/commit/ac58445989aee8c21905b9d91d7f9d18b0ab5427) (newest on `main`; the branch point [`871d623`](https://github.com/gandr-lang/gandr/commit/871d62326a92b16d78d12de7c1a8f10cb9bca7c4) has no report)
Wall time `412.30 ms → 528.87 ms` **+28%**

**Functions · timing**
⚠️ [`gandr_core_checker::module::decide`](https://github.com/gandr-lang/gandr/blob/def8465ee289cd7d95d3e79cdee0d64ff0c20ae7/crates/core-checker/src/module.rs#L1045): avg `190.88 µs → 251.64 µs` **+32%** · fails the check
⚠️ [`gandr_theory_coherent_resolutions::rewrite::normalize`](https://github.com/gandr-lang/gandr/blob/def8465ee289cd7d95d3e79cdee0d64ff0c20ae7/crates/theory-coherent-resolutions/src/rewrite.rs#L171): avg `7.76 µs → 9.79 µs` **+26%** · fails the check
⚠️ [`gandr_theory_coherent_resolutions::overlap::interior_overlaps_between`](https://github.com/gandr-lang/gandr/blob/def8465ee289cd7d95d3e79cdee0d64ff0c20ae7/crates/theory-coherent-resolutions/src/overlap.rs#L1054): avg `6.74 µs → 8.30 µs` **+23%** · fails the check
";

    /// A failed `gandr-timing` check naming `decide` and `normalize`.
    const TWO: &str = "**Functions · timing**
⚠️ [`gandr_core_checker::module::decide`](https://github.com/gandr-lang/gandr/blob/76dd52f/crates/core-checker/src/module.rs#L1009): avg `100.00 µs → 140.00 µs` **+40%** · fails the check
⚠️ [`gandr_theory_coherent_resolutions::rewrite::normalize`](https://github.com/gandr-lang/gandr/blob/76dd52f/crates/theory-coherent-resolutions/src/rewrite.rs#L171): avg `100.00 µs → 108.00 µs` **+8.0%** · fails the check
";

    /// What each site of `section` files as under `reading`.
    ///
    /// # Specification
    /// trivial.
    fn filings(
        section: &Section,
        reading: Maybe<&Reading, Unread>,
    ) -> Vec<Filing>
    {
        let judgement = section.judged(reading);
        section
            .sites
            .iter()
            .map(|site| judgement.filing(site))
            .collect()
    }

    #[test]
    fn a_uniform_timing_shift_is_a_runner_shift()
    {
        // A timing report: each `(name, average in µs)` of `rows`, and a wall
        // time of `wall` milliseconds.
        let report = |rows: &[(String, u64)], wall: u64| {
            let data = rows
                .iter()
                .map(|&(ref name, avg)| {
                    serde_json::json!({
                        "name": name,
                        "calls": 50_u64,
                        "avg": format!("{avg} µs"),
                        "total": format!("{} µs", avg.checked_mul(50).unwrap()),
                        "percent_total": "1.00%",
                    })
                })
                .collect::<Vec<_>>();
            let text = serde_json::json!({
                "functions_timing": {
                    "total_elapsed_ns": wall.checked_mul(1_000_000).unwrap(),
                    "data": data,
                },
            })
            .to_string();
            Run::read(Input {
                path: "report.json",
                text: &text,
            })
            .unwrap()
        };
        let sections = |summary: &str| {
            Failure::read(
                Benchmark("gandr-timing".into()),
                RunUrl("https://github.com/gandr-lang/gandr/runs/1".into()),
                &Summary(summary.to_owned()),
            )
            .sections
        };
        let policy = Policy::read(Input {
            path: "gandr-timing-policy.toml",
            text: include_str!("../../../hotpath/gandr-timing-policy.toml"),
        })
        .unwrap();
        let fixture = |text: &str| {
            Run::read(Input {
                path: "gandr-timing.json",
                text,
            })
            .unwrap()
        };
        let Maybe::Present(replayed) = Reading::read(
            fixture(include_str!(
                "../tests/reports/hotpath-ac58445989aee8c21905b9d91d7f9d18b0ab5427/gandr-timing.json"
            )),
            fixture(include_str!(
                "../tests/reports/hotpath-73f2e468d48dfd25332b479e7ee451195301e227/gandr-timing.json"
            )),
            &policy,
        )
        else {
            panic!("the replayed run reads a shift");
        };
        let [ref timing] = *sections(REPLAYED)
        else {
            panic!("one timing section");
        };
        let shift = replayed.shift();
        assert_eq!(
            shift.ratio.to_string(),
            "+27.2",
            "the median over 16 functions"
        );
        assert!(matches!(
            timing.judged(Maybe::Present(&replayed)),
            Judgement::Shifted(_)
        ));
        assert_eq!(
            filings(timing, Maybe::Present(&replayed)),
            [Filing::Shifted(shift); 3],
            "`decide` at +31.8 % is +3.7 % beside the runner's +27.2 %"
        );
        assert_eq!(
            filings(timing, Maybe::Absent(Unread::Few)),
            [Filing::Regressed; 3],
            "no shift read: each site files as the check names it"
        );
        let [ref allocations] = *sections(&REPLAYED.replace("· timing", "· allocations"))
        else {
            panic!("one allocation section");
        };
        assert_eq!(
            filings(allocations, Maybe::Present(&replayed)),
            [Filing::Regressed; 3],
            "an allocation section is never judged against the timing shift"
        );

        let others = (0_u8 .. 12).map(|index| (format!("function {index}"), 102));
        let rows = |decide: u64| {
            let mut rows = vec![
                ("gandr_core_checker::module::decide".to_owned(), decide),
                (
                    "gandr_theory_coherent_resolutions::rewrite::normalize".to_owned(),
                    108,
                ),
            ];
            rows.extend(others.clone());
            rows
        };
        let base = report(
            &rows(100)
                .into_iter()
                .map(|(name, _)| (name, 100))
                .collect::<Vec<_>>(),
            100,
        );
        let Maybe::Present(one) = Reading::read(base.clone(), report(&rows(140), 102), &policy)
        else {
            panic!("14 functions read a shift");
        };
        assert_eq!(one.shift().ratio.to_string(), "+2");
        let [ref two] = *sections(TWO)
        else {
            panic!("one timing section");
        };
        assert_eq!(
            filings(two, Maybe::Present(&one)),
            [Filing::Regressed, Filing::Within],
            "+40 % beside +2 % regresses; +8 % beside it, +5.9 %, does not"
        );
        let Maybe::Present(quiet) = Reading::read(base, report(&rows(102), 102), &policy)
        else {
            panic!("14 functions read a shift");
        };
        assert!(
            matches!(two.judged(Maybe::Present(&quiet)), Judgement::Relative(_)),
            "a runner at +2 % is no shift, though no site crosses beside it"
        );
        assert_eq!(filings(two, Maybe::Present(&quiet)), [
            Filing::Within,
            Filing::Within
        ]);
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
