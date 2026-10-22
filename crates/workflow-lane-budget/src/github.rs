//! The runs and jobs a report samples, and the one issue it files, through
//! `gh`, which resolves the repository from `GH_REPO` or the checkout.

use core::fmt;
use std::io::Write as _;
use std::process::Command;
use std::process::Stdio;

use serde::Deserialize;

use crate::budget::RunCount;
use crate::error::BudgetError;
use crate::report::Report;
use crate::report::RunId;
use crate::report::Sample;
use crate::report::Standing;

/// The `gh api` route listing the CI workflow's runs.
const RUNS: &str = "repos/{owner}/{repo}/actions/workflows/ci.yml/runs";

/// The `gh api` route listing the nightly workflow's runs.
const NIGHTLY_RUNS: &str = "repos/{owner}/{repo}/actions/workflows/nightly.yml/runs";

/// The query keeping the runs a landing window samples: merge-queue and
/// pull-request runs, newest first.
const RUN_QUERY: &str =
    r#".workflow_runs[] | select(.event == "merge_group" or .event == "pull_request") | .id"#;

/// The query listing every run of a listing already narrowed to scheduled
/// runs, newest first.
const SCHEDULED_QUERY: &str = ".workflow_runs[] | .id";

/// Which workflow runs a report samples.
///
/// # Specification
/// - provides: the three windows a report reads.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Window
{
    /// Merge-queue and pull-request runs of the CI workflow, which hold every
    /// landing lane.
    Landing,
    /// The CI workflow's daily scheduled runs, which alone hold the daily
    /// lanes.
    Scheduled,
    /// The nightly workflow's scheduled runs, which hold the nightly lanes.
    Nightly,
}

/// The query printing each successful job's seconds and name.
const JOB_QUERY: &str = r#".jobs[] | select(.conclusion == "success") | "\((.completed_at | fromdate) - (.started_at | fromdate))\t\(.name)""#;

/// The title of the one issue the report files.
#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IssueTitle(String);

impl From<&str> for IssueTitle
{
    /// Titles the issue `title`.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the issue is opened under the title given, so an
    ///   emptied title changes the invocation logged.
    /// - witness: `tests::cli::an_over_budget_lane_opens_the_issue`
    #[inline]
    fn from(title: &str) -> Self
    {
        Self(title.to_owned())
    }
}

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
    ///
    /// # Adequacy
    /// - hypothesis: L3 — the closed, reopened and updated issue are each named
    ///   by number in the line printed.
    /// - witness: `tests::cli::an_issue_follows_the_budget_both_ways`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        write!(f, "#{}", self.0)
    }
}

/// What filing the report did to the issue.
///
/// # Specification
/// - provides: the line the binary prints after the report.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Filed
{
    /// No issue had the title and a lane was over: one was opened, at the
    /// address `gh` printed.
    Opened(String),
    /// The open issue's body is now this report.
    Updated(IssueNumber),
    /// The closed issue's body is now this report, and it is open again.
    Reopened(IssueNumber),
    /// Every lane was within budget: the open issue's body is this report,
    /// and it is closed.
    Closed(IssueNumber),
    /// Every lane was within budget and no issue was open.
    Untouched,
}

impl fmt::Display for Filed
{
    /// Writes one sentence naming the action and the issue.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — every action's line is asserted, so writing nothing
    ///   changes each.
    /// - witness: `tests::cli::an_over_budget_lane_opens_the_issue`
    /// - witness: `tests::cli::an_issue_follows_the_budget_both_ways`
    #[inline]
    fn fmt(
        &self,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    {
        match *self {
            Self::Opened(ref url) => write!(f, "Opened {url}."),
            Self::Updated(number) => write!(f, "Updated {number}."),
            Self::Reopened(number) => write!(f, "Reopened {number}."),
            Self::Closed(number) => write!(f, "Closed {number}: every lane is within budget."),
            Self::Untouched => f.write_str("Every lane is within budget; no issue is open."),
        }
    }
}

/// One issue as `gh issue list --json number,state,title` prints it.
#[derive(Debug, Deserialize)]
struct Listed
{
    /// The issue's number.
    number: u64,
    /// `OPEN` or `CLOSED`.
    state: String,
    /// The issue's title.
    title: String,
}

/// What a `gh` invocation reads on standard input.
#[derive(Clone, Copy, Debug)]
pub enum Feed<'report>
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
/// - fails: [`BudgetError::Gh`], naming the invocation, when the command cannot
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
/// - witness: `tests::cli::an_over_budget_lane_opens_the_issue`
/// - witness: `tests::cli::a_failing_gh_is_reported_with_its_message`
pub(crate) fn run(
    command: &mut Command,
    feed: Feed<'_>,
) -> Result<String, BudgetError>
{
    let label = format!("{command:?}");
    let refuse = |message: String| BudgetError::Gh {
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

/// The newest runs in `window`.
///
/// # Specification
/// - requires: `gh` on the path, authenticated for the repository.
/// - ensures: at most `count` run identifiers, newest first: for
///   [`Window::Landing`] the CI workflow's merge-queue and pull-request runs
///   among its last hundred completed runs; for [`Window::Scheduled`] its last
///   completed scheduled runs, which the listing itself narrows to, since a
///   day's hundred landing runs would crowd them out; for [`Window::Nightly`]
///   the nightly workflow's last completed scheduled runs, a dispatch left out.
/// - provides: the window a report samples.
/// - fails: [`BudgetError::Gh`] when `gh` fails or prints a line that is not a
///   run identifier.
/// - panics: none.
/// - executable: none — the outcome is the external process's.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a fake `gh` listing three landing runs read with a count
///   of two yields the first two; one printing garbage is refused; the
///   scheduled window asks for scheduled runs alone and reads its own list; the
///   nightly window asks the nightly workflow for its scheduled runs.
/// - witness: `tests::cli::an_over_budget_lane_opens_the_issue`
/// - witness: `tests::cli::a_failing_gh_is_reported_with_its_message`
/// - witness: `tests::cli::a_daily_lane_is_sampled_over_the_scheduled_runs`
/// - witness: `tests::cli::a_nightly_lane_is_sampled_over_the_nightly_runs`
#[inline]
pub fn recent_runs(
    count: RunCount,
    window: Window,
) -> Result<Vec<RunId>, BudgetError>
{
    let mut command = Command::new("gh");
    command.args([
        "api",
        "--method",
        "GET",
        match window {
            Window::Landing | Window::Scheduled => RUNS,
            Window::Nightly => NIGHTLY_RUNS,
        },
        "-f",
        "status=completed",
        "-f",
        "per_page=100",
    ]);
    match window {
        Window::Landing => command.args(["--jq", RUN_QUERY]),
        Window::Scheduled | Window::Nightly => {
            command.args(["-f", "event=schedule", "--jq", SCHEDULED_QUERY])
        },
    };
    let text = run(&mut command, Feed::Nothing)?;
    text.lines()
        .take(usize::from(count))
        .map(|line| {
            line.parse::<RunId>().map_err(|error| BudgetError::Gh {
                command: format!("{command:?}"),
                message: format!("`{line}` is not a run identifier: {error}"),
            })
        })
        .collect()
}

/// The successful jobs of `run`, each with its time.
///
/// # Specification
/// - requires: `gh` on the path, authenticated for the repository.
/// - ensures: one sample per successful job `gh` lists for the run.
/// - provides: a run's contribution to every lane's median.
/// - fails: [`BudgetError::Gh`] when `gh` fails or prints a line that is not a
///   sample.
/// - panics: none.
/// - executable: none — the outcome is the external process's.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a fake `gh` printing two jobs per run feeds each lane's
///   median; a run's jobs dropped or misattributed changes the report.
/// - witness: `tests::cli::an_over_budget_lane_opens_the_issue`
#[inline]
pub fn samples(run_id: RunId) -> Result<Vec<Sample>, BudgetError>
{
    let mut command = Command::new("gh");
    command.args([
        "api",
        "--method",
        "GET",
        &format!("repos/{{owner}}/{{repo}}/actions/runs/{run_id}/jobs"),
        "-f",
        "per_page=100",
        "--jq",
        JOB_QUERY,
    ]);
    let text = run(&mut command, Feed::Nothing)?;
    text.lines()
        .map(|line| {
            line.parse::<Sample>().ok().ok_or_else(|| BudgetError::Gh {
                command: format!("{command:?}"),
                message: format!("`{line}` is not a job's seconds and name"),
            })
        })
        .collect()
}

/// Files `report` on the one issue titled `title`: opened or updated while a
/// lane is over budget, closed once every lane is within.
///
/// # Specification
/// - requires: `gh` on the path, authenticated for the repository with
///   permission to write issues.
/// - ensures: when the report is over, the issue with exactly that title,
///   opened if none exists and reopened if closed, holds the report as its
///   body; when it is within, an open such issue holds the report and is
///   closed, and a closed or absent one is left alone.
/// - provides: one issue per repository, never one per night.
/// - fails: [`BudgetError::Gh`] when a `gh` invocation fails or the listing is
///   not the JSON this crate reads.
/// - panics: none.
/// - executable: none — the outcome is the repository's issue state.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a fake `gh` holding no issue, an open one and a closed
///   one, run over and within budget; filing a second issue, editing a closed
///   one while within, or leaving an open one open changes the recorded
///   invocations.
/// - witness: `tests::cli::an_over_budget_lane_opens_the_issue`
/// - witness: `tests::cli::an_issue_follows_the_budget_both_ways`
#[inline]
pub fn file(
    report: &Report,
    title: &IssueTitle,
) -> Result<Filed, BudgetError>
{
    let mut list = Command::new("gh");
    list.args([
        "issue",
        "list",
        "--state",
        "all",
        "--limit",
        "100",
        "--search",
        &format!("\"{}\" in:title", title.0),
        "--json",
        "number,state,title",
    ]);
    let listing = run(&mut list, Feed::Nothing)?;
    let issues: Vec<Listed> = serde_json::from_str(&listing).map_err(|error| BudgetError::Gh {
        command: format!("{list:?}"),
        message: error.to_string(),
    })?;
    let found = issues.into_iter().find(|issue| issue.title == title.0);
    let edit = |number: u64| {
        run(
            Command::new("gh").args(["issue", "edit", &number.to_string(), "--body-file", "-"]),
            Feed::Body(report),
        )
    };
    let act = |verb: &str, number: u64| {
        run(
            Command::new("gh").args(["issue", verb, &number.to_string()]),
            Feed::Nothing,
        )
    };
    match (report.standing(), found) {
        (Standing::Over, None) => {
            let url = run(
                Command::new("gh").args([
                    "issue",
                    "create",
                    "--title",
                    &title.0,
                    "--body-file",
                    "-",
                ]),
                Feed::Body(report),
            )?;
            Ok(Filed::Opened(url.trim().to_owned()))
        },
        (Standing::Over, Some(issue)) => {
            edit(issue.number)?;
            if issue.state == "OPEN" {
                Ok(Filed::Updated(IssueNumber(issue.number)))
            }
            else {
                act("reopen", issue.number)?;
                Ok(Filed::Reopened(IssueNumber(issue.number)))
            }
        },
        (Standing::Within | Standing::Unmeasured, Some(issue)) if issue.state == "OPEN" => {
            edit(issue.number)?;
            act("close", issue.number)?;
            Ok(Filed::Closed(IssueNumber(issue.number)))
        },
        (Standing::Within | Standing::Unmeasured, _) => Ok(Filed::Untouched),
    }
}
