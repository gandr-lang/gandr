//! `lane-budget`: each budgeted CI lane's median job time over the latest
//! merge-queue and pull-request runs, against its budget.
//!
//! `lane-budget --budget NAME=SECONDS... [--daily NAME=SECONDS...] [--nightly
//! NAME=SECONDS...] [--summed NAME=BUDGET/CEILING...] [--runs N] [--issue
//! TITLE]` samples the newest `N` runs through `gh`, classifies each by the
//! cone its landing touched, and, with `--daily`, samples the CI workflow's
//! newest `N` scheduled runs for the lanes only they hold; with `--nightly`,
//! the nightly workflow's; with `--summed`, every active workflow's newest `N`
//! completed runs, timed whole, and the cache's usage. It prints the Markdown
//! report and with `--issue` opens, updates, reopens or closes the one issue of
//! that title.
//!
//! # Exit codes
//!
//! - `0`: the report was printed and filed, whatever it found; also `--help`
//!   and `--version`.
//! - `2`: a refusal — a malformed budget, a deep daily or nightly budget, a
//!   failed `gh` invocation, or standard output closed; also a malformed
//!   invocation.

use core::str::FromStr;
use std::io::Write as _;
use std::process::ExitCode;

use anodized::spec;
use gandr_workflow_lane_budget::Budget;
use gandr_workflow_lane_budget::BudgetError;
use gandr_workflow_lane_budget::Cone;
use gandr_workflow_lane_budget::IssueTitle;
use gandr_workflow_lane_budget::Report;
use gandr_workflow_lane_budget::RunCount;
use gandr_workflow_lane_budget::Summed;
use gandr_workflow_lane_budget::Workflows;
use gandr_workflow_lane_budget::cone;
use gandr_workflow_lane_budget::github;
use gandr_workflow_lane_budget::github::Jobs;
use gandr_workflow_lane_budget::github::Window;

/// The exit code of a refusal or a malformed invocation.
const REFUSED: u8 = 2;

/// Each budgeted CI lane's median job time against its budget.
#[derive(Debug, clap::Parser)]
#[command(name = "lane-budget", version, about)]
struct Cli
{
    /// A job's display name, an optional `:deep` or `:surface` cone, and the
    /// whole seconds its median may take, as `NAME=SECONDS` or
    /// `NAME:deep=SECONDS`; repeat for each lane and cone.
    #[arg(long = "budget", required = true)]
    budgets: Vec<Budget>,
    /// How many of the newest runs of each window to sample.
    #[arg(long, default_value = "10")]
    runs: RunCount,
    /// A lane only the daily scheduled run holds and the whole seconds its
    /// median over the scheduled runs may take, as `NAME=SECONDS`; such a lane
    /// is not cone-classified, so a deep budget is refused.
    #[arg(long = "daily")]
    daily: Vec<Unclassified>,
    /// A lane of the nightly workflow and the whole seconds its median over
    /// that workflow's scheduled runs may take, as `NAME=SECONDS`; such a lane
    /// is not cone-classified, so a deep budget is refused.
    #[arg(long = "nightly")]
    nightly: Vec<Unclassified>,
    /// A workflow's budget for the lower median of its runs' summed job time
    /// and the ceiling no run's may pass, in whole seconds, as
    /// `NAME=BUDGET/CEILING`; any adds the table of every active workflow's
    /// runs timed whole and the cache's usage.
    #[arg(long = "summed")]
    summed: Vec<Summed>,
    /// The title of the one issue to open while a lane is over budget and to
    /// close once every lane is within.
    #[arg(long)]
    issue: Option<String>,
}

/// A `--daily` or `--nightly` budget: a `--budget` of the surface cone.
#[repr(transparent)]
#[derive(Clone, Debug)]
struct Unclassified(Budget);

impl FromStr for Unclassified
{
    type Err = BudgetError;

    /// Reads `NAME=SECONDS` as [`Budget`] does, refusing the deep cone.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the budget `text` names, of the surface cone.
    /// - provides: the daily and nightly budget tables from the workflow's
    ///   arguments.
    /// - fails: [`BudgetError::Budget`] as [`Budget`]'s parse fails;
    ///   [`BudgetError::Scheduled`] when `text` names the deep cone.
    /// - panics: none.
    /// - executable: none — the outcome is the parse itself.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — a deep daily budget is refused; accepting a cone a
    ///   scheduled window never classifies changes the exit code.
    /// - witness: `tests::cli::a_malformed_budget_exits_two`
    #[inline]
    fn from_str(text: &str) -> Result<Self, Self::Err>
    {
        let budget = text.parse::<Budget>()?;
        if budget.cone == Cone::Deep {
            return Err(BudgetError::Scheduled {
                text: text.to_owned(),
            });
        }
        Ok(Self(budget))
    }
}

/// Parses the invocation, reports and chooses the exit code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: exits `0` after printing the report and the filing, help or
///   version; exits `2` after printing a refusal or a usage message to standard
///   error.
/// - provides: the process boundary.
/// - fails: never; every refusal is an exit code.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a report filed over budget, one within, a failing `gh`
///   and a malformed budget; a swapped stream or exit code changes the observed
///   process result.
/// - witness: `tests::cli::an_over_budget_lane_opens_the_issue`
/// - witness: `tests::cli::a_failing_gh_is_reported_with_its_message`
/// - witness: `tests::cli::a_malformed_budget_exits_two`
#[spec(ensures: |ret| ret == ExitCode::SUCCESS || ret == ExitCode::from(REFUSED))]
fn main() -> ExitCode
{
    let cli = match <Cli as clap::Parser>::try_parse() {
        Ok(cli) => cli,
        Err(error) => {
            return match (error.print(), error.use_stderr()) {
                (Ok(()), false) => ExitCode::SUCCESS,
                (Ok(()), true) | (Err(_), _) => ExitCode::from(REFUSED),
            };
        },
    };
    match run(cli) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => match writeln!(std::io::stderr(), "lane-budget: {error}") {
            Ok(()) | Err(_) => ExitCode::from(REFUSED),
        },
    }
}

/// Samples the runs, prints the report and files it.
///
/// # Specification
/// - requires: `gh` on the path, authenticated for the repository.
/// - ensures: standard output receives the report, its daily table sampled only
///   with `--daily`, its nightly table only with `--nightly` and its workflow
///   table only with `--summed`, then, with `--issue`, one line naming what
///   filing did.
/// - provides: the whole command.
/// - fails: every refusal of [`github::recent_runs`], [`github::samples`],
///   [`github::timed`], [`github::cache_usage`] and [`github::file`];
///   [`BudgetError::Output`] when standard output cannot be written.
/// - panics: none.
/// - executable: none — the outcome is the bytes on standard output and the
///   repository's issue.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — as [`main`].
/// - witness: `tests::cli::an_over_budget_lane_opens_the_issue`
/// - witness: `tests::cli::an_issue_follows_the_budget_both_ways`
/// - witness: `tests::cli::a_daily_lane_is_sampled_over_the_scheduled_runs`
/// - witness: `tests::cli::a_nightly_lane_is_sampled_over_the_nightly_runs`
/// - witness: `tests::cli::a_summed_budget_tables_every_workflow`
fn run(cli: Cli) -> Result<(), BudgetError>
{
    let runs = github::recent_runs(cli.runs, Window::Landing)?;
    let mut samples = Vec::new();
    for &run_id in &runs {
        let cone = cone::classify(run_id)?;
        for sample in github::samples(run_id, Jobs::Successful)? {
            samples.push((cone, sample));
        }
    }
    let mut report = Report::new(&cli.budgets, runs, samples);
    for (window, budgets) in [
        (Window::Scheduled, cli.daily),
        (Window::Nightly, cli.nightly),
    ] {
        if budgets.is_empty() {
            continue;
        }
        let budgets: Vec<Budget> = budgets
            .into_iter()
            .map(|Unclassified(budget)| budget)
            .collect();
        let runs = github::recent_runs(cli.runs, window)?;
        let mut samples = Vec::new();
        for &run_id in &runs {
            samples.extend(github::samples(run_id, Jobs::Successful)?);
        }
        report = report.with_scheduled(window, &budgets, runs, samples);
    }
    if !cli.summed.is_empty() {
        let timed = github::timed(cli.runs)?;
        let cache = github::cache_usage()?;
        report = report.with_workflows(Workflows::new(&cli.summed, cli.runs, timed, cache));
    }
    let output = |error: std::io::Error| BudgetError::Output {
        message: error.to_string(),
    };
    write!(std::io::stdout(), "{report}").map_err(output)?;
    if let Some(title) = cli.issue {
        let filed = github::file(&report, &IssueTitle::from(title.as_str()))?;
        writeln!(std::io::stdout(), "\n{filed}").map_err(output)?;
    }
    Ok(())
}
