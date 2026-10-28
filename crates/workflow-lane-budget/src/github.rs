//! The runs and jobs a report samples, and the one issue it files, through
//! `gh`, which resolves the repository from `GH_REPO` or the checkout.

use core::fmt;
use core::sync::atomic::AtomicBool;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;
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
use crate::workflows::CacheUsage;
use crate::workflows::Timed;
use crate::workflows::WorkflowName;

/// The label marking the issue the report keeps: its body is the report, and
/// it closes once every lane is within budget.
const COLLECTOR: &str = "collector";

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

/// The query printing each completed job's seconds and name, whatever its
/// conclusion: a failed or cancelled job's time counts in its run's sum.
const COMPLETED_JOB_QUERY: &str = r#".jobs[] | select(.completed_at != null and .started_at != null) | "\((.completed_at | fromdate) - (.started_at | fromdate) | if . < 0 then 0 else . end)\t\(.name)""#;

/// The `gh api` route listing the repository's workflows.
const WORKFLOWS: &str = "repos/{owner}/{repo}/actions/workflows";

/// The query printing each active workflow's identifier and name.
const WORKFLOW_QUERY: &str = r#".workflows[] | select(.state == "active") | "\(.id)\t\(.name)""#;

/// The query printing each listed run's identifier and wall seconds, from its
/// start to its last update.
const TIMED_QUERY: &str = r#".workflow_runs[] | "\(.id)\t\((.updated_at | fromdate) - (.run_started_at | fromdate) | if . < 0 then 0 else . end)""#;

/// The `gh api` route reporting the repository's Actions cache usage.
const CACHE: &str = "repos/{owner}/{repo}/actions/cache/usage";

/// The query printing the active caches' bytes and count.
const CACHE_QUERY: &str = r#""\(.active_caches_size_in_bytes)\t\(.active_caches_count)""#;

/// Which of a run's jobs [`samples`] reads.
///
/// # Specification
/// - provides: the two readings of a run's jobs.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Jobs
{
    /// The successful jobs: a lane's median is a time its job took to pass.
    Successful,
    /// Every completed job: a run's summed time counts what it spent.
    Completed,
}

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

/// How many `gh` reads run at once. Each read is a process waiting on the
/// network, and a night's report makes over a hundred of them: one at a time,
/// the nightly's lane-budget step took 120 s, past its job's 133 s share with
/// the job's other steps; eight at a time the same reads took a fifth as long
/// locally. GitHub's secondary rate limit refuses far more concurrent
/// requests than this.
const READS: usize = 8;

/// `read` applied to each of `items`, at most [`READS`] at once, the results
/// in `items`' order.
///
/// # Specification
/// - requires: nothing.
/// - ensures: when every read succeeds, one result per item, the `i`-th being
///   `read` of the `i`-th item, so what is built from them is what reading them
///   one at a time builds; otherwise the refusal of the first item, in `items`'
///   order, whose read failed. Once a read fails no item not yet taken is read;
///   every item before it was taken first, so its refusal is still the first in
///   order.
/// - provides: the concurrent reads of a report's runs and workflows.
/// - fails: the first failing read's refusal; [`BudgetError::Reader`] when a
///   reading thread cannot start or stops without its results.
/// - panics: none.
/// - executable: none — the reads are the caller's, external processes here.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — reads that finish in the reverse of the asked order come
///   back in the asked order; of two failing reads the earlier is reported; a
///   result placed by finishing order, or the later refusal reported, changes
///   the asserted value.
/// - witness: `github::tests::reads_come_back_in_the_asked_order`
/// - witness: `github::tests::the_first_refusal_in_order_is_reported`
#[inline]
pub fn read_all<Item, Read, Reader>(
    items: &[Item],
    read: Reader,
) -> Result<Vec<Read>, BudgetError>
where
    Item: Sync,
    Read: Send,
    Reader: Fn(&Item) -> Result<Read, BudgetError> + Sync,
{
    let next = AtomicUsize::new(0);
    let failed = AtomicBool::new(false);
    let worker = || {
        let mut done = Vec::new();
        while !failed.load(Ordering::Acquire) {
            let index = next.fetch_add(1, Ordering::AcqRel);
            let Some(item) = items.get(index)
            else {
                break;
            };
            let result = read(item);
            if result.is_err() {
                failed.store(true, Ordering::Release);
            }
            done.push((index, result));
        }
        done
    };
    let mut done = std::thread::scope(|scope| {
        let mut workers = Vec::new();
        for _ in 0 .. READS.min(items.len()) {
            workers.push(
                std::thread::Builder::new()
                    .spawn_scoped(scope, worker)
                    .map_err(|error| BudgetError::Reader {
                        message: error.to_string(),
                    }),
            );
        }
        let mut done = Vec::new();
        for spawned in workers {
            let reads = spawned?.join().map_err(|_panic| BudgetError::Reader {
                message: String::from("the thread stopped without its reads"),
            })?;
            done.extend(reads);
        }
        Ok(done)
    })?;
    done.sort_unstable_by_key(|&(index, _)| index);
    done.into_iter().map(|(_, result)| result).collect()
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

/// The successful or the completed jobs of `run`, as `jobs` asks, each with
/// its time.
///
/// # Specification
/// - requires: `gh` on the path, authenticated for the repository.
/// - ensures: one sample per job `gh` lists for the run that `jobs` admits: a
///   successful one for [`Jobs::Successful`], any completed one for
///   [`Jobs::Completed`].
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
/// - witness: `tests::cli::a_summed_budget_tables_every_workflow`
#[inline]
pub fn samples(
    run_id: RunId,
    jobs: Jobs,
) -> Result<Vec<Sample>, BudgetError>
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
        match jobs {
            Jobs::Successful => JOB_QUERY,
            Jobs::Completed => COMPLETED_JOB_QUERY,
        },
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

/// Every active workflow with its newest completed runs timed.
///
/// # Specification
/// - requires: `gh` on the path, authenticated for the repository.
/// - ensures: one entry per active workflow, in the listing's order, holding at
///   most `count` of its newest completed runs, newest first, each with its
///   wall time and its completed jobs.
/// - provides: what the workflow table summarises.
/// - fails: [`BudgetError::Gh`] when `gh` fails or prints a line that is not a
///   workflow, a timed run or a job.
/// - panics: none.
/// - executable: none — the outcome is the external process's.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a fake `gh` listing two workflows, one with three runs
///   read with a count of two; a workflow's runs attributed to another, a run's
///   jobs dropped or the count ignored changes the table.
/// - witness: `tests::cli::a_summed_budget_tables_every_workflow`
#[inline]
pub fn timed(count: RunCount) -> Result<Vec<(WorkflowName, Vec<Timed>)>, BudgetError>
{
    let mut list = Command::new("gh");
    list.args([
        "api",
        "--method",
        "GET",
        WORKFLOWS,
        "-f",
        "per_page=100",
        "--jq",
        WORKFLOW_QUERY,
    ]);
    let listing = run(&mut list, Feed::Nothing)?;
    let unread = |command: &Command, line: &str, what: &str| BudgetError::Gh {
        command: format!("{command:?}"),
        message: format!("`{line}` is not {what}"),
    };
    let per_page = format!("per_page={}", usize::from(count));
    let mut workflows = Vec::new();
    for line in listing.lines() {
        let (id, name) = line
            .split_once('\t')
            .filter(|&(id, name)| !name.is_empty() && id.parse::<u64>().is_ok())
            .ok_or_else(|| unread(&list, line, "a workflow's identifier and name"))?;
        workflows.push((id, WorkflowName::from(name)));
    }
    let listed = read_all(&workflows, |&(id, _)| {
        let route = format!("repos/{{owner}}/{{repo}}/actions/workflows/{id}/runs");
        let mut runs = Command::new("gh");
        runs.args([
            "api",
            "--method",
            "GET",
            &route,
            "-f",
            "status=completed",
            "-f",
            &per_page,
            "--jq",
            TIMED_QUERY,
        ]);
        let text = run(&mut runs, Feed::Nothing)?;
        text.lines()
            .take(usize::from(count))
            .map(|line| {
                line.split_once('\t')
                    .and_then(|(run_id, wall)| {
                        Some((run_id.parse::<RunId>().ok()?, wall.parse().ok()?))
                    })
                    .ok_or_else(|| unread(&runs, line, "a run's identifier and wall seconds"))
            })
            .collect::<Result<Vec<_>, _>>()
    })?;
    let walls: Vec<_> = listed.iter().flatten().copied().collect();
    let jobs = read_all(&walls, |&(run_id, _)| samples(run_id, Jobs::Completed))?;
    let mut runs = walls
        .into_iter()
        .zip(jobs)
        .map(|((run, wall), jobs)| Timed { run, wall, jobs });
    Ok(workflows
        .into_iter()
        .zip(listed)
        .map(|((_, name), listed)| (name, runs.by_ref().take(listed.len()).collect()))
        .collect())
}

/// The repository's Actions cache usage.
///
/// # Specification
/// - requires: `gh` on the path, authenticated for the repository.
/// - ensures: the active caches' bytes and count as GitHub reports them.
/// - provides: the workflow table's cache line.
/// - fails: [`BudgetError::Gh`] when `gh` fails or prints what is not a usage.
/// - panics: none.
/// - executable: none — the outcome is the external process's.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a fake `gh` reporting a usage read into the table; a
///   usage invented or a route misnamed changes the cache line.
/// - witness: `tests::cli::a_summed_budget_tables_every_workflow`
#[inline]
pub fn cache_usage() -> Result<CacheUsage, BudgetError>
{
    let mut command = Command::new("gh");
    command.args(["api", "--method", "GET", CACHE, "--jq", CACHE_QUERY]);
    let text = run(&mut command, Feed::Nothing)?;
    text.parse::<CacheUsage>()
        .ok()
        .ok_or_else(|| BudgetError::Gh {
            command: format!("{command:?}"),
            message: format!("`{}` is not the caches' bytes and count", text.trim()),
        })
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
///   closed, and a closed or absent one is left alone. Every issue opened or
///   edited carries [`COLLECTOR`].
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
            Command::new("gh").args([
                "issue",
                "edit",
                &number.to_string(),
                "--body-file",
                "-",
                "--add-label",
                COLLECTOR,
            ]),
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
                    "--label",
                    COLLECTOR,
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

#[cfg(test)]
mod tests
{
    use core::time::Duration;

    use super::read_all;
    use crate::error::BudgetError;

    #[test]
    fn reads_come_back_in_the_asked_order()
    {
        let items: Vec<u64> = (0 .. 24).collect();
        // Each read waits the longer the earlier it was asked, so they finish
        // in the reverse of the asked order.
        let read = read_all(&items, |&item| {
            std::thread::sleep(Duration::from_millis(24_u64.saturating_sub(item)));
            Ok(item.saturating_mul(2))
        });
        assert_eq!(
            read,
            Ok(items.iter().map(|item| item.saturating_mul(2)).collect())
        );
    }

    #[test]
    fn the_first_refusal_in_order_is_reported()
    {
        let items: Vec<u64> = (0 .. 24).collect();
        let refused = |item: u64| BudgetError::Gh {
            command: format!("gh api runs/{item}/jobs"),
            message: String::from("HTTP 502"),
        };
        // The earlier refusal is the slower: the later one is met first.
        let read = read_all(&items, |&item| {
            std::thread::sleep(Duration::from_millis(if item == 3 { 60 } else { 1 }));
            if item == 3 || item == 17 {
                Err(refused(item))
            }
            else {
                Ok(item)
            }
        });
        assert_eq!(read, Err(refused(3)));
    }
}
