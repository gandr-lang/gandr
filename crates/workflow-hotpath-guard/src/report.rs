//! One commit's failed hotpath checks, as the issue that names its pull
//! request: the title, the labels and the Markdown body.

extern crate alloc;

use alloc::collections::BTreeSet;
use core::fmt;

use anodized::spec;
use quenchant_shape::shape::Maybe;
use serde::Deserialize;

use crate::check::AreaLabel;
use crate::check::CommitSha;
use crate::check::Failure;
use crate::check::Repository;

/// The opening every title the guard files carries, before its subject.
pub const TITLE_PREFIX: &str = "perf: ";

/// The label every issue the guard files carries.
pub const KIND: &str = "kind:performance";

/// How long a title's list of sites may grow before the rest is counted.
const TITLE_SITES: usize = 120;

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
    /// Its labels.
    labels: Vec<ListedLabel>,
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

/// A label as GitHub answers it.
#[repr(transparent)]
#[derive(Debug, Deserialize)]
struct ListedLabel
{
    /// The label's name.
    name: String,
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
    /// Its `area:` labels.
    areas: BTreeSet<AreaLabel>,
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
            areas: pull
                .labels
                .into_iter()
                .filter_map(|label| label.name.parse::<AreaLabel>().ok())
                .collect(),
        }),
        None => Maybe::Absent(Unpulled),
    }
}

/// Whether the commit calls for the issue.
///
/// # Specification
/// trivial.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Standing
{
    /// At least one hotpath check failed.
    Regressed,
    /// No hotpath check failed: nothing is filed.
    Clear,
}

/// A commit's failed hotpath checks and the pull request they name.
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
}

impl Report
{
    /// The report of `sha`'s failed checks.
    ///
    /// # Specification
    /// trivial.
    #[must_use]
    #[inline]
    pub const fn new(
        repository: Repository,
        sha: CommitSha,
        pull: Maybe<Pull, Unpulled>,
        failures: Vec<Failure>,
    ) -> Self
    {
        Self {
            repository,
            sha,
            pull,
            failures,
        }
    }

    /// Whether any hotpath check failed.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Standing::Regressed`] exactly when a failure is held.
    /// - provides: the verdict the issue is filed by.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a commit with two failed checks and one with none;
    ///   filing the clear one or not the other changes the invocations.
    /// - witness: `tests::cli::a_failed_check_opens_the_issue`
    /// - witness: `tests::cli::a_clear_commit_files_nothing`
    #[spec(ensures: |ret| matches!(ret, Standing::Regressed) != self.failures.is_empty())]
    #[must_use]
    #[inline]
    pub fn standing(&self) -> Standing
    {
        if self.failures.is_empty() {
            Standing::Clear
        }
        else {
            Standing::Regressed
        }
    }

    /// The title's opening that finds the subject's issue: `perf: #1358
    /// regresses ` for a pull request, `perf: 914a768 regresses ` for a
    /// commit none carries.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`TITLE_PREFIX`], the pull request's number or the commit's
    ///   short form, then ` regresses `.
    /// - provides: the key of the one issue per pull request.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a pull request's opening and a bare commit's; a
    ///   missing space or the branch in place of the number lets one pull
    ///   request's issue match another's.
    /// - witness: `tests::cli::a_later_run_updates_the_pull_request_issue`
    /// - witness: `tests::cli::a_commit_without_a_pull_request_is_filed_by_its_sha`
    #[spec(ensures: |ret| ret.0.starts_with(TITLE_PREFIX) && ret.0.ends_with(" regresses "))]
    #[must_use]
    #[inline]
    pub fn key(&self) -> IssueKey
    {
        IssueKey(match self.pull {
            Maybe::Present(ref pull) => format!("{TITLE_PREFIX}{} regresses ", pull.number),
            Maybe::Absent(_) => format!("{TITLE_PREFIX}{} regresses ", self.sha.short()),
        })
    }

    /// The issue's title: the key, then the regressed sites.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`Report::key`] followed by each distinct site's short name
    ///   in reading order, comma-separated, while the list stays within 120
    ///   bytes, then `and <n> more` for the rest; the failed benchmarks' names
    ///   when no site was read.
    /// - provides: the title the issue is opened or retitled with.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a real regression's five sites across two checks, one
    ///   repeated, and a check without sites; a repeated site, a lost one or an
    ///   empty title changes it.
    /// - witness: `tests::cli::a_failed_check_opens_the_issue`
    /// - witness: `report::tests::a_long_list_of_sites_is_counted`
    #[spec(ensures: |ret| ret.0.starts_with(self.key().0.as_str()))]
    #[must_use]
    #[inline]
    pub fn title(&self) -> IssueTitle
    {
        let mut seen = BTreeSet::new();
        let mut names: Vec<String> = Vec::new();
        for site in self
            .failures
            .iter()
            .flat_map(|failure| failure.sections.iter())
            .flat_map(|section| section.sites.iter())
        {
            let name = site.name.short();
            if seen.insert(name.clone()) {
                names.push(name.to_string());
            }
        }
        if names.is_empty() {
            names = self
                .failures
                .iter()
                .map(|failure| failure.benchmark.to_string())
                .collect();
        }
        let mut list = String::new();
        let mut kept = 0_usize;
        for name in &names {
            let grown = list.len().saturating_add(name.len()).saturating_add(2);
            if kept > 0 && grown > TITLE_SITES {
                break;
            }
            if kept > 0 {
                list.push_str(", ");
            }
            list.push_str(name);
            kept = kept.saturating_add(1);
        }
        let rest = names.len().saturating_sub(kept);
        if rest > 0 {
            list.push_str(" and ");
            list.push_str(&rest.to_string());
            list.push_str(" more");
        }
        IssueTitle(format!("{}{list}", self.key().0))
    }

    /// The labels the issue carries: [`KIND`], the pull request's areas and
    /// the areas of the crates the sites live in.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: [`KIND`] first, then the union of the pull request's `area:`
    ///   labels and each site's crate tier, sorted, each once.
    /// - provides: the labels triage routes by: the authoring lane's area and
    ///   the area the regression shows in.
    /// - fails: never.
    /// - panics: none.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a pull request labelled `area:theory` regressing
    ///   sites in `core-checker` and `surface-driver`; dropping the pull
    ///   request's area or a site's changes the labels.
    /// - witness: `tests::cli::a_failed_check_opens_the_issue`
    #[spec(ensures: |ret| ret.first().map(String::as_str) == Some(KIND))]
    #[must_use]
    #[inline]
    pub fn labels(&self) -> Vec<String>
    {
        let mut areas: BTreeSet<AreaLabel> = match self.pull {
            Maybe::Present(ref pull) => pull.areas.clone(),
            Maybe::Absent(_) => BTreeSet::new(),
        };
        for site in self
            .failures
            .iter()
            .flat_map(|failure| failure.sections.iter())
            .flat_map(|section| section.sites.iter())
        {
            if let Maybe::Present(ref krate) = site.krate
                && let Maybe::Present(area) = krate.area()
            {
                areas.insert(area);
            }
        }
        core::iter::once(KIND.to_owned())
            .chain(areas.into_iter().map(|area| area.to_string()))
            .collect()
    }
}

/// The opening of a title that finds the one issue of a subject.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IssueKey(String);

impl fmt::Display for IssueKey
{
    /// Writes the opening, its trailing space included.
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

/// An issue's title.
#[repr(transparent)]
#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
pub struct IssueTitle(String);

impl fmt::Display for IssueTitle
{
    /// Writes the title.
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

impl fmt::Display for Report
{
    /// Writes the issue's body: the subject, each failed check with its run,
    /// wall-time line and sites, and the `## Lint` heading the fix fills.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: a sentence naming the pull request, its branch and the commit
    ///   (or the commit alone), then one `##` section per failed check linking
    ///   its run with its wall-time line and each metric's sites as a list,
    ///   then `## Lint` with the question the fix answers; a clear report
    ///   writes one sentence saying no check failed.
    /// - provides: the body the issue carries and the job summary prints.
    /// - fails: propagates the formatter's own write failure.
    /// - panics: none.
    /// - executable: none — the formatter exposes no readable output buffer.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a real regression's two failed checks; a lost run
    ///   link, wall line, site or the lint heading changes the asserted body.
    /// - witness: `tests::cli::a_failed_check_opens_the_issue`
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
            "The check is not required, so nothing waited for it. The triage lane routes \
             this issue to the authoring lane; a later failed run updates it."
        )?;
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
        writeln!(
            f,
            "\n## Lint\n\nThe fix states whether a quenchant dylint could have refused the \
             pattern that regressed, as the rule it would check. When it could, the lint \
             lands in quenchant and on gandr's lint wall at once and is named here; when \
             it could not, one sentence says why."
        )
    }
}

#[cfg(test)]
mod tests
{
    use quenchant_shape::shape::Maybe;

    use super::ListedHead;
    use super::ListedLabel;
    use super::ListedPull;
    use super::PullNumber;
    use super::Report;
    use super::pull_of;

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
                labels: vec![ListedLabel {
                    name: "area:theory".to_owned(),
                }],
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
    fn a_long_list_of_sites_is_counted()
    {
        let summary = (0_u32 .. 12)
            .map(|index| {
                format!(
                    "⚠️ [`gandr_core_checker::module::site_number_{index}`](https://github.com/x/blob/y/crates/core-checker/src/module.rs#L1): avg `1 → 2` **+100%** · fails the check"
                )
            })
            .collect::<Vec<_>>()
            .join("\n");
        let listed: crate::check::Listed = serde_json::from_value(serde_json::json!({
            "name": "hotpath / gandr",
            "status": "completed",
            "conclusion": "failure",
            "html_url": "https://github.com/gandr-lang/gandr/runs/1",
            "summary": summary,
        }))
        .unwrap();
        let Maybe::Present(failure) = listed.failure()
        else {
            panic!("a completed failed hotpath check is a failure");
        };
        let report = Report::new(
            "gandr-lang/gandr".parse().unwrap(),
            "914a768".parse().unwrap(),
            Maybe::Absent(super::Unpulled),
            vec![failure],
        );
        let title = report.title().to_string();
        assert!(
            title.starts_with("perf: 914a768 regresses module::site_number_0, "),
            "{title}"
        );
        assert!(title.ends_with(" and 7 more"), "{title}");
    }
}
