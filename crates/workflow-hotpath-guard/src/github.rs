//! A commit's checks and pull request, and the one issue per pull request,
//! through `gh`, which resolves the repository of an `issue` command from
//! `GH_REPO` or the checkout.

use core::fmt;
use std::io::Write as _;
use std::process::Command;
use std::process::Stdio;

use quenchant_shape::shape::Maybe;
use serde::Deserialize;

use crate::check::CommitSha;
use crate::check::Failure;
use crate::check::Listed;
use crate::check::Repository;
use crate::error::GuardError;
use crate::report::ListedPull;
use crate::report::Pull;
use crate::report::Report;
use crate::report::Standing;
use crate::report::TITLE_PREFIX;
use crate::report::Unpulled;
use crate::report::pull_of;

/// An issue's number in the repository.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct IssueNumber(u64);

impl fmt::Display for IssueNumber
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

/// What filing the report did.
///
/// # Specification
/// - provides: the line the binary prints after the report.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Filed
{
    /// A check failed and the subject had no open issue: one was opened, at
    /// the address `gh` printed.
    Opened(String),
    /// A check failed and the subject's issue was open: its title, body and
    /// labels now state this run.
    Updated(IssueNumber),
    /// No hotpath check failed: no issue was read or written.
    Untouched,
}

impl fmt::Display for Filed
{
    /// Writes one sentence naming the action and the issue.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Opened(ref url) => write!(f, "Opened {url}."),
            Self::Updated(number) => write!(f, "Updated {number}."),
            Self::Untouched => f.write_str("No hotpath check failed; no issue filed."),
        }
    }
}

/// One issue as `gh issue list --json number,title` prints it.
#[derive(Debug, Deserialize)]
struct ListedIssue
{
    /// The issue's number.
    number: u64,
    /// The issue's title.
    title: String,
}

/// What a `gh` invocation reads on standard input.
#[derive(Clone, Copy, Debug)]
enum Feed<'report>
{
    /// Nothing: standard input stays the parent's.
    Nothing,
    /// The report, as the issue body `--body-file -` reads.
    Body(&'report Report),
}

/// Runs `command`, feeding it `feed` on standard input, and returns what it
/// wrote to standard output.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the command's standard output, read as UTF-8 with any invalid
///   sequence replaced.
/// - provides: the one place a `gh` invocation's failure becomes a refusal.
/// - fails: [`GuardError::Gh`], naming the invocation, when the command cannot
///   start, its input cannot be written, or it exits unsuccessfully; the
///   message is its standard error.
/// - panics: none.
/// - executable: none — the outcome is the external process's.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a fake `gh` that succeeds, one that fails with a message,
///   and one that records the body it was fed; a swallowed exit status, a lost
///   message or an unfed body changes the observed result.
/// - witness: `tests::cli::a_failed_check_opens_the_issue`
/// - witness: `tests::cli::a_failing_gh_is_reported_with_its_message`
fn run(
    command: &mut Command,
    feed: Feed<'_>,
) -> Result<String, GuardError>
{
    let label = format!("{command:?}");
    let refuse = |message: String| GuardError::Gh {
        command: label.clone(),
        message,
    };
    command.stdout(Stdio::piped()).stderr(Stdio::piped());
    if let Feed::Body(_) = feed {
        command.stdin(Stdio::piped());
    }
    let mut child = command.spawn().map_err(|error| refuse(error.to_string()))?;
    if let (Feed::Body(report), Some(mut stdin)) = (feed, child.stdin.take()) {
        stdin
            .write_all(report.to_string().as_bytes())
            .map_err(|error| refuse(error.to_string()))?;
    }
    let output = child
        .wait_with_output()
        .map_err(|error| refuse(error.to_string()))?;
    if !output.status.success() {
        return Err(refuse(format!(
            "{}: {}",
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        )));
    }
    Ok(String::from_utf8_lossy(&output.stdout).into_owned())
}

/// The failed `hotpath / <benchmark>` checks of `sha`.
///
/// # Specification
/// - requires: `gh` on the path, authenticated for the repository.
/// - ensures: every completed `hotpath / ` check of the commit whose conclusion
///   is `failure`, in the order GitHub lists them, each read by
///   [`Failure::read`]; every page of the listing is read.
/// - provides: the checks a report is made of, all of them at once, so the
///   event of each failed benchmark files the same issue.
/// - fails: [`GuardError::Gh`] when the query fails or a line it prints is not
///   the JSON this crate reads.
/// - panics: none.
/// - executable: none — the outcome is the external process's.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a commit whose listing holds two failed hotpath checks, a
///   passing one, a pending one and a failed check of another name; reading any
///   of the last three as a failure changes the report.
/// - witness: `tests::cli::only_a_completed_failed_hotpath_check_is_filed`
#[inline]
pub fn failures(
    repository: &Repository,
    sha: &CommitSha,
) -> Result<Vec<Failure>, GuardError>
{
    let mut query = Command::new("gh");
    query.args([
        "api",
        "--paginate",
        &format!("repos/{repository}/commits/{sha}/check-runs?per_page=100"),
        "--jq",
        ".check_runs[] | {name, status, conclusion, html_url, summary: (.output.summary // \"\")}",
    ]);
    let listing = run(&mut query, Feed::Nothing)?;
    let mut failures = Vec::new();
    for line in listing.lines().filter(|line| !line.trim().is_empty()) {
        let listed: Listed = serde_json::from_str(line).map_err(|error| GuardError::Gh {
            command: format!("{query:?}"),
            message: error.to_string(),
        })?;
        if let Maybe::Present(failure) = listed.failure() {
            failures.push(failure);
        }
    }
    Ok(failures)
}

/// The pull request `sha` names.
///
/// # Specification
/// - requires: `gh` on the path, authenticated for the repository.
/// - ensures: the pull request GitHub associates with the commit that it heads,
///   else the first it lists; absent when it lists none.
/// - provides: the subject of the one issue.
/// - fails: [`GuardError::Gh`] when the query fails or prints what this crate
///   does not read.
/// - panics: none.
/// - executable: none — the outcome is the external process's.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a commit a pull request heads and one none carries;
///   inventing a pull request or losing one changes the title.
/// - witness: `tests::cli::a_failed_check_opens_the_issue`
/// - witness: `tests::cli::a_commit_without_a_pull_request_is_filed_by_its_sha`
#[inline]
pub fn pull(
    repository: &Repository,
    sha: &CommitSha,
) -> Result<Maybe<Pull, Unpulled>, GuardError>
{
    let mut query = Command::new("gh");
    query.args(["api", &format!("repos/{repository}/commits/{sha}/pulls")]);
    let answer = run(&mut query, Feed::Nothing)?;
    let listed: Vec<ListedPull> =
        serde_json::from_str(&answer).map_err(|error| GuardError::Gh {
            command: format!("{query:?}"),
            message: error.to_string(),
        })?;
    Ok(pull_of(sha, listed))
}

/// Files `report` on its subject's one open issue: opened when none is open,
/// retitled, rewritten and relabelled when one is; nothing when no check
/// failed.
///
/// # Specification
/// - requires: `gh` on the path, authenticated for the repository with
///   permission to write issues.
/// - ensures: when the report stands [`Standing::Regressed`], the open issue
///   whose title starts with [`Report::key`] carries the report's title, body
///   and labels, opened with them if none was open; when it stands
///   [`Standing::Clear`], no `gh` invocation runs.
/// - provides: one open issue per pull request, updated by each later failed
///   run; a closed one is history and stays closed.
/// - fails: [`GuardError::Gh`] when a `gh` invocation fails or the listing is
///   not the JSON this crate reads.
/// - panics: none.
/// - executable: none — the outcome is the repository's issue state.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a fake `gh` holding no issue for the pull request, one
///   holding its issue beside another pull request's whose number it prefixes,
///   and a clear commit; opening a second issue, editing the other pull
///   request's or touching any issue while clear changes the recorded
///   invocations.
/// - witness: `tests::cli::a_failed_check_opens_the_issue`
/// - witness: `tests::cli::a_later_run_updates_the_pull_request_issue`
/// - witness: `tests::cli::a_clear_commit_files_nothing`
#[inline]
pub fn file(report: &Report) -> Result<Filed, GuardError>
{
    if report.standing() == Standing::Clear {
        return Ok(Filed::Untouched);
    }
    let key = report.key().to_string();
    let title = report.title().to_string();
    let labels = report.labels();
    let mut list = Command::new("gh");
    list.args([
        "issue",
        "list",
        "--state",
        "open",
        "--limit",
        "100",
        "--search",
        &format!("\"{}\" in:title", key.trim_end()),
        "--json",
        "number,title",
    ]);
    let listing = run(&mut list, Feed::Nothing)?;
    let issues: Vec<ListedIssue> =
        serde_json::from_str(&listing).map_err(|error| GuardError::Gh {
            command: format!("{list:?}"),
            message: error.to_string(),
        })?;
    if let Some(issue) = issues
        .into_iter()
        .find(|issue| issue.title.starts_with(TITLE_PREFIX) && issue.title.starts_with(&key))
    {
        let mut edit = Command::new("gh");
        edit.args([
            "issue",
            "edit",
            &issue.number.to_string(),
            "--title",
            &title,
            "--body-file",
            "-",
        ]);
        for label in &labels {
            edit.args(["--add-label", label]);
        }
        run(&mut edit, Feed::Body(report))?;
        return Ok(Filed::Updated(IssueNumber(issue.number)));
    }
    let mut create = Command::new("gh");
    create.args(["issue", "create", "--title", &title, "--body-file", "-"]);
    for label in &labels {
        create.args(["--label", label]);
    }
    let url = run(&mut create, Feed::Body(report))?;
    Ok(Filed::Opened(url.trim().to_owned()))
}
