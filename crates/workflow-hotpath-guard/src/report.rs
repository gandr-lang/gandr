//! One commit's concluded hotpath checks and the pull request they name: the
//! regressions each function's index records, and the report a regression's
//! comment carries.

extern crate alloc;

use alloc::collections::BTreeMap;
use alloc::collections::BTreeSet;
use core::fmt;
use core::str::FromStr;

use anodized::spec;
use quenchant_shape::shape::Maybe;
use serde::Deserialize;

use crate::check::Benchmark;
use crate::check::CommitSha;
use crate::check::Concluded;
use crate::check::CrateDir;
use crate::check::Failure;
use crate::check::Repository;
use crate::check::RunUrl;
use crate::check::Shift;
use crate::check::SiteName;
use crate::check::SummaryLine;
use crate::check::Unshifted;
use crate::check::Unstated;

/// A pull request's number.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PullNumber(u64);

impl fmt::Display for PullNumber
{
    /// Writes `#` and the number.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "#{}", self.0)
    }
}

/// The marker that closes the hotpath verdict's task line in a pull
/// request's body.
pub const VERDICT_MARKER: &str = "<!-- ack hotpath-verdict -->";

/// The opening of an accepted hotpath verdict, after its ticked box.
pub const ACCEPTED: &str = "hotpath: accepted — ";

/// A pull request's Markdown body, as GitHub answers it.
#[repr(transparent)]
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq)]
#[serde(transparent)]
pub struct PullBody(pub String);

impl PullBody
{
    /// The growth the body accepts, by benchmark: each ticked hotpath verdict
    /// in the accepted shape.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one entry per benchmark a line accepts, where the line is a
    ///   ticked task closed by [`VERDICT_MARKER`] whose text reads `hotpath:
    ///   accepted — <benchmark> exercises <feature>; <n> allocations per <use>;
    ///   <sentence>`, its acceptance that text after [`ACCEPTED`]; the first
    ///   line kept for a benchmark accepted twice. An unticked line, a `fixed`
    ///   verdict and a line of another shape accept nothing.
    /// - provides: the regressions a landing settles as accepted. The
    ///   obligation the merge passed through holds the full shape; this reads
    ///   what it settled.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the scan is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a ticked accepted line, the same benchmark accepted
    ///   again, an unticked one, a ticked `fixed` one and one without its
    ///   sentence; reading any but the first as an acceptance, or losing it,
    ///   changes the rows a landing settles.
    /// - witness: `report::tests::a_ticked_accepted_verdict_accepts_its_benchmark`
    #[must_use]
    #[inline]
    pub fn accepted(&self) -> BTreeMap<Benchmark, Acceptance>
    {
        let mut accepted = BTreeMap::new();
        for line in self.0.lines().map(str::trim) {
            let Some(verdict) = line
                .strip_prefix("- [x] ")
                .or_else(|| line.strip_prefix("- [X] "))
                .and_then(|rest| rest.strip_suffix(VERDICT_MARKER))
                .and_then(|rest| rest.trim_end().strip_prefix(ACCEPTED))
            else {
                continue;
            };
            let Some((benchmark, cost)) = verdict.split_once(" exercises ")
            else {
                continue;
            };
            if cost.splitn(3, "; ").nth(2).is_some() {
                let Ok(benchmark) = benchmark.parse::<Benchmark>();
                accepted
                    .entry(benchmark)
                    .or_insert_with(|| Acceptance(verdict.to_owned()));
            }
        }
        accepted
    }
}

/// An accepted hotpath verdict's text after [`ACCEPTED`]: `<benchmark>
/// exercises <feature>; <n> allocations per <use>; <sentence>`.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Acceptance(String);

impl fmt::Display for Acceptance
{
    /// Writes the verdict as a table cell holds it, each `|` escaped.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a verdict holding a `|` reads back escaped, and an
    ///   accepted landing's row carries the verdict whole; an empty or
    ///   unescaped cell changes both.
    /// - witness: `report::tests::a_ticked_accepted_verdict_accepts_its_benchmark`
    /// - witness: `tests::cli::an_accepted_landing_settles_its_issue_without_a_comment`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        f.write_str(&self.0.replace('|', "\\|"))
    }
}

/// Why a regression is not accepted: its pull request's body accepts no
/// growth on its benchmark, or no pull request carries it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Unaccepted;

/// One pull request as `gh api repos/<repository>/commits/<sha>/pulls`
/// answers it.
#[derive(Debug, Deserialize)]
pub(crate) struct ListedPull
{
    /// Its number.
    number: u64,
    /// Its page.
    html_url: String,
    /// Its head.
    head: ListedHead,
    /// Its body, null when it has none.
    #[serde(default)]
    body: Option<PullBody>,
}

/// A pull request's head as GitHub answers it.
#[derive(Debug, Deserialize)]
struct ListedHead
{
    /// The branch.
    #[serde(rename = "ref")]
    branch: String,
    /// The head commit.
    sha: String,
}

/// The pull request a failed check names.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Pull
{
    /// Its number.
    pub number: PullNumber,
    /// Its page.
    url: String,
    /// Its branch.
    branch: String,
    /// The growth its body accepts, by benchmark.
    accepted: BTreeMap<Benchmark, Acceptance>,
}

/// Why a commit names no pull request: none carries it.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Unpulled;

/// The pull request of `sha` among the ones GitHub associates with it.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the pull request whose head is `sha` when one is listed;
///   otherwise the first listed; absent when none is.
/// - provides: the pull request a stack's shared commit names: the one it
///   heads, not a later one that carries it.
/// - fails: never.
/// - panics: none.
/// - executable: none — the search is the clause.
///
/// # Adequacy
/// - hypothesis: L3 — a stack listing a later pull request before the one the
///   commit heads, and an empty listing; taking the first listed, or inventing
///   a pull request, changes the subject.
/// - witness: `report::tests::a_commit_names_the_pull_request_it_heads`
#[inline]
pub(crate) fn pull_of(
    sha: &CommitSha,
    listed: Vec<ListedPull>,
) -> Maybe<Pull, Unpulled>
{
    let head = sha.to_string();
    let mut first = None;
    let mut headed = None;
    for pull in listed {
        if pull.head.sha == head {
            headed = Some(pull);
            break;
        }
        if first.is_none() {
            first = Some(pull);
        }
    }
    match headed.or(first) {
        Some(pull) => Maybe::Present(Pull {
            number: PullNumber(pull.number),
            url: pull.html_url,
            branch: pull.head.branch,
            accepted: pull.body.unwrap_or_default().accepted(),
        }),
        None => Maybe::Absent(Unpulled),
    }
}

/// What a row of an index is keyed by: the pull request, `#1358`, or the
/// commit no pull request carries, `` `914a768` ``.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Subject(String);

impl FromStr for Subject
{
    type Err = core::convert::Infallible;

    /// Reads a row's first cell as written.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from_str(text: &str) -> Result<Self, Self::Err>
    {
        Ok(Self(text.to_owned()))
    }
}

impl fmt::Display for Subject
{
    /// Writes the subject as an index's first cell holds it.
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

/// One function's regression in one failed check: what its index row states.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Regression
{
    /// The function, by its profiled name.
    pub function: SiteName,
    /// The crate its source lives in.
    pub krate: Maybe<CrateDir, Unstated>,
    /// The benchmark whose check failed.
    pub series: Benchmark,
    /// The check's page.
    pub run: RunUrl,
    /// The metric: `allocations` or `timing`.
    pub metric: SummaryLine,
    /// The before/after numbers: `` avg `1444 → 2558` **+77%** ``.
    pub delta: SummaryLine,
    /// The runner shift the check reads as, if it is one.
    pub shift: Maybe<Shift, Unshifted>,
    /// The growth the pull request's body accepts on this benchmark, if it
    /// accepts any.
    pub accepted: Maybe<Acceptance, Unaccepted>,
}

/// A commit's concluded hotpath checks and the pull request they name.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Report
{
    /// The repository.
    repository: Repository,
    /// The commit the checks ran on.
    sha: CommitSha,
    /// The pull request the commit heads or is carried by.
    pull: Maybe<Pull, Unpulled>,
    /// The failed checks, in the order GitHub lists them.
    failures: Vec<Failure>,
    /// The passed checks' benchmarks, each with its page.
    passed: BTreeMap<Benchmark, RunUrl>,
}

impl Report
{
    /// The report of `sha`'s concluded checks.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the failed checks in their order, and each passed check's
    ///   benchmark with its page, the first listed kept for a benchmark listed
    ///   twice.
    /// - provides: the report a run files.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the split is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a failed, a passed and a second passed check of one
    ///   benchmark; a failure kept as passed, or the later page kept, changes
    ///   the rows.
    /// - witness: `tests::cli::only_a_completed_failed_hotpath_check_is_filed`
    /// - witness: `tests::cli::a_passing_run_marks_its_row_fixed_without_a_comment`
    #[must_use]
    #[inline]
    pub fn new(
        repository: Repository,
        sha: CommitSha,
        pull: Maybe<Pull, Unpulled>,
        checks: Vec<Concluded>,
    ) -> Self
    {
        let mut failures = Vec::new();
        let mut passed = BTreeMap::new();
        for check in checks {
            match check {
                Concluded::Failed(failure) => failures.push(failure),
                Concluded::Passed { benchmark, run } => {
                    passed.entry(benchmark).or_insert(run);
                },
            }
        }
        Self {
            repository,
            sha,
            pull,
            failures,
            passed,
        }
    }

    /// The repository the checks ran in.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn repository(&self) -> &Repository
    {
        &self.repository
    }

    /// The commit the checks ran on.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn sha(&self) -> &CommitSha
    {
        &self.sha
    }

    /// The benchmarks whose checks passed, each with its page.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn passed(&self) -> &BTreeMap<Benchmark, RunUrl>
    {
        &self.passed
    }

    /// The key of the report's rows: the pull request's number, or the
    /// commit's short form in backquotes when no pull request carries it.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: `#<n>` for a pull request; `` `<short>` `` for a bare commit.
    /// - provides: the first cell of every row this run writes, so a later run
    ///   of the same pull request finds its row.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a pull request's subject and a bare commit's; the
    ///   branch for the number, or the full commit, misses the earlier row.
    /// - witness: `tests::cli::a_commit_without_a_pull_request_is_filed_by_its_sha`
    /// - witness: `tests::cli::a_later_run_updates_its_row_without_a_comment`
    #[spec(ensures: |ret| ret.0.starts_with('#') || ret.0.starts_with('`'))]
    #[must_use]
    #[inline]
    pub fn subject(&self) -> Subject
    {
        Subject(match self.pull {
            Maybe::Present(ref pull) => pull.number.to_string(),
            Maybe::Absent(_) => format!("`{}`", self.sha.short()),
        })
    }

    /// Each function the failed checks regressed, once per benchmark.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: one regression per distinct function and failed benchmark,
    ///   from the first site naming it, in reading order; its metric is the
    ///   section heading after `Functions · `, its delta the site's line after
    ///   its link, its shift [`Failure::shift`] over the commit's failures, and
    ///   its acceptance the one the pull request's body states for its
    ///   benchmark (see [`PullBody::accepted`]).
    /// - provides: the rows this run writes.
    /// - fails: never.
    /// - panics: none.
    /// - executable: none — the walk is the clause.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — two failed checks naming `decide` once each and a
    ///   second site in one; a merged benchmark, a lost site or a link left in
    ///   the delta changes the rows.
    /// - witness: `tests::cli::a_failed_check_opens_one_issue_per_function`
    #[must_use]
    #[inline]
    pub fn regressions(&self) -> Vec<Regression>
    {
        let mut seen = BTreeSet::new();
        let mut regressions = Vec::new();
        for failure in &self.failures {
            let shift = failure.shift(&self.failures);
            let accepted = self.accepted(&failure.benchmark);
            for section in &failure.sections {
                for site in &section.sites {
                    if !seen.insert((&site.name, &failure.benchmark)) {
                        continue;
                    }
                    regressions.push(Regression {
                        function: site.name.clone(),
                        krate: site.krate.clone(),
                        series: failure.benchmark.clone(),
                        run: failure.run.clone(),
                        metric: section.metric.metric(),
                        delta: site.line.delta(),
                        shift,
                        accepted: accepted.clone(),
                    });
                }
            }
        }
        regressions
    }

    /// The growth the pull request's body accepts on `benchmark`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a landing whose body accepts `gandr` alone, failing
    ///   `gandr` alone and beside `gandr-timing`: reading its benchmark as
    ///   unaccepted files the accepted regression and comments on its issue.
    /// - witness: `tests::cli::an_accepted_landing_settles_its_issue_without_a_comment`
    /// - witness: `tests::cli::an_unaccepted_benchmark_beside_an_accepted_one_still_files`
    fn accepted(
        &self,
        benchmark: &Benchmark,
    ) -> Maybe<Acceptance, Unaccepted>
    {
        match self.pull {
            Maybe::Present(ref pull) => pull
                .accepted
                .get(benchmark)
                .map_or(Maybe::Absent(Unaccepted), |acceptance| {
                    Maybe::Present(acceptance.clone())
                }),
            Maybe::Absent(_) => Maybe::Absent(Unaccepted),
        }
    }

    /// The functions the failed checks regressed, by name, sorted, each once.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub fn regressed(&self) -> BTreeSet<SiteName>
    {
        self.failures
            .iter()
            .flat_map(|failure| failure.sections.iter())
            .flat_map(|section| section.sites.iter())
            .map(|site| site.name.clone())
            .collect()
    }
}

impl fmt::Display for Report
{
    /// Writes the report a regression's comment carries: the subject, each
    /// failed check with its run, wall-time line and sites.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a sentence naming the pull request, its branch and the commit
    ///   (or the commit alone); for a pull request, a sentence naming each
    ///   failed benchmark its body accepts no growth on, the missing verdict,
    ///   or saying it accepts them all; then one `##` section per failed check
    ///   linking its run with its wall-time line and each metric's sites as a
    ///   list; a report without a failure writes one sentence saying no check
    ///   failed.
    /// - provides: the comment the guard appends and the job summary prints.
    /// - fails: propagates the formatter's own write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a real regression's two failed checks, and a landing
    ///   whose body accepts its growth; a lost run link, wall line, site or
    ///   missing verdict changes the asserted comment.
    /// - witness: `tests::cli::a_failed_check_opens_one_issue_per_function`
    /// - witness: `tests::cli::a_landing_with_an_accepted_verdict_files_no_issue`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        let commit = format!(
            "[`{}`](https://github.com/{}/commit/{})",
            self.sha.short(),
            self.repository,
            self.sha
        );
        if self.failures.is_empty() {
            return writeln!(f, "No hotpath check failed at {commit}.");
        }
        match self.pull {
            Maybe::Present(ref pull) => writeln!(
                f,
                "A hotpath check failed on [{}]({}) (`{}`) at {commit}.",
                pull.number, pull.url, pull.branch
            )?,
            Maybe::Absent(_) => writeln!(
                f,
                "A hotpath check failed at {commit}, which no pull request carries."
            )?,
        }
        writeln!(
            f,
            "The check is not required, so nothing waited for it. The index above holds \
             this regression's row."
        )?;
        if matches!(self.pull, Maybe::Present(_)) {
            let unaccepted = self
                .failures
                .iter()
                .filter(|failure| matches!(self.accepted(&failure.benchmark), Maybe::Absent(_)))
                .map(|failure| format!("`{}`", failure.benchmark))
                .collect::<Vec<_>>();
            if unaccepted.is_empty() {
                writeln!(
                    f,
                    "Its body accepts this growth with a settled hotpath verdict, so its rows \
                     read `accepted`."
                )?;
            }
            else {
                writeln!(
                    f,
                    "Its body carries no settled `{ACCEPTED}<benchmark> …` verdict for {}: \
                     the hotpath verdict is missing.",
                    unaccepted.join(", ")
                )?;
            }
        }
        for failure in &self.failures {
            writeln!(f, "\n## `hotpath / {}`\n", failure.benchmark)?;
            match failure.wall {
                Maybe::Present(ref wall) => writeln!(f, "[The run]({}). {wall}", failure.run)?,
                Maybe::Absent(_) => writeln!(f, "[The run]({}).", failure.run)?,
            }
            for section in &failure.sections {
                writeln!(f, "\n**{}**\n", section.metric)?;
                for site in &section.sites {
                    writeln!(f, "- {}", site.line)?;
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests
{
    use quenchant_shape::shape::Maybe;

    use super::Acceptance;
    use super::ListedHead;
    use super::ListedPull;
    use super::PullBody;
    use super::PullNumber;
    use super::pull_of;
    use crate::check::Benchmark;

    /// A listed pull request numbered `$number` whose head is `$sha`.
    macro_rules! listed {
        ($number:expr, $sha:literal) => {
            ListedPull {
                number: $number,
                html_url: format!("https://github.com/gandr-lang/gandr/pull/{}", $number),
                head: ListedHead {
                    branch: format!("branch-{}", $number),
                    sha: $sha.to_owned(),
                },
                body: None,
            }
        };
    }

    #[test]
    fn a_commit_names_the_pull_request_it_heads()
    {
        let sha = "914a768fb32501be92e5cb4d28ce6613dfa01022".parse().unwrap();
        let stack = vec![
            listed!(1362_u64, "b52c58585c2365b2e677525bc33723d1019aa2c5"),
            listed!(1358_u64, "914a768fb32501be92e5cb4d28ce6613dfa01022"),
        ];
        match pull_of(&sha, stack) {
            Maybe::Present(pull) => assert_eq!(pull.number, PullNumber(1358)),
            Maybe::Absent(_) => panic!("the stack holds the pull request the commit heads"),
        }
        let carried = vec![listed!(
            1362_u64,
            "b52c58585c2365b2e677525bc33723d1019aa2c5"
        )];
        assert!(matches!(pull_of(&sha, carried), Maybe::Present(_)));
        assert!(matches!(pull_of(&sha, Vec::new()), Maybe::Absent(_)));
    }

    #[test]
    fn a_ticked_accepted_verdict_accepts_its_benchmark()
    {
        let marker = super::VERDICT_MARKER;
        let body = PullBody(format!(
            "### Hotpath\n\n- [x] hotpath: accepted — gandr exercises records; 31 allocations \
             per record; an arena | a pool loses {marker}\n- [x] hotpath: accepted — gandr \
             exercises other; 1 allocations per x; later {marker}\n- [ ] hotpath: accepted — \
             store exercises blobs; 2 allocations per blob; a sentence {marker}\n- [x] hotpath: \
             fixed — gandr-timing 235 → 179 {marker}\n- [X] hotpath: accepted — gandr-timing \
             exercises records; 31 allocations per record {marker}\n- [x] hotpath: accepted — \
             store exercises blobs; 2 allocations per blob; a sentence\n"
        ));
        let gandr = Acceptance(
            "gandr exercises records; 31 allocations per record; an arena | a pool loses"
                .to_owned(),
        );
        assert_eq!(
            body.accepted().into_iter().collect::<Vec<_>>(),
            [("gandr".parse::<Benchmark>().unwrap(), gandr.clone())],
            "the first ticked accepted line alone; unticked, fixed, sentence-less and unmarked \
             lines accept nothing"
        );
        assert_eq!(
            gandr.to_string(),
            "gandr exercises records; 31 allocations per record; an arena \\| a pool loses",
            "a table cell escapes its bar"
        );
        assert!(PullBody::default().accepted().is_empty());
    }
}
