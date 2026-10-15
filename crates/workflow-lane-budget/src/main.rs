//! `lane-budget`: each budgeted CI lane's median job time over the latest
//! merge-queue and pull-request runs, against its budget.
//!
//! `lane-budget --budget NAME=SECONDS... [--runs N] [--issue TITLE]` samples
//! the newest `N` runs through `gh`, classifies each by the cone its landing
//! touched, prints the Markdown report, and with `--issue` opens, updates,
//! reopens or closes the one issue of that title.
//!
//! # Exit codes
//!
//! - `0`: the report was printed and filed, whatever it found; also `--help`
//!   and `--version`.
//! - `2`: a refusal — a malformed budget, a failed `gh` invocation, or standard
//!   output closed; also a malformed invocation.

use std::io::Write as _;
use std::process::ExitCode;

use anodized::spec;
use gandr_workflow_lane_budget::Budget;
use gandr_workflow_lane_budget::BudgetError;
use gandr_workflow_lane_budget::IssueTitle;
use gandr_workflow_lane_budget::Report;
use gandr_workflow_lane_budget::RunCount;
use gandr_workflow_lane_budget::cone;
use gandr_workflow_lane_budget::github;

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
    /// How many of the newest merge-queue and pull-request runs to sample.
    #[arg(long, default_value = "10")]
    runs: RunCount,
    /// The title of the one issue to open while a lane is over budget and to
    /// close once every lane is within.
    #[arg(long)]
    issue: Option<String>,
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
/// - witness: `cli::cli::an_over_budget_lane_opens_the_issue`
/// - witness: `cli::cli::a_failing_gh_is_reported_with_its_message`
/// - witness: `cli::cli::a_malformed_budget_exits_two`
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
/// - ensures: standard output receives the report, then, with `--issue`, one
///   line naming what filing did.
/// - provides: the whole command.
/// - fails: every refusal of [`github::recent_runs`], [`github::samples`] and
///   [`github::file`]; [`BudgetError::Output`] when standard output cannot be
///   written.
/// - panics: none.
/// - executable: none — the outcome is the bytes on standard output and the
///   repository's issue.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — as [`main`].
/// - witness: `cli::cli::an_over_budget_lane_opens_the_issue`
/// - witness: `cli::cli::an_issue_follows_the_budget_both_ways`
fn run(cli: Cli) -> Result<(), BudgetError>
{
    let runs = github::recent_runs(cli.runs)?;
    let mut samples = Vec::new();
    for &run_id in &runs {
        let cone = cone::classify(run_id)?;
        for sample in github::samples(run_id)? {
            samples.push((cone, sample));
        }
    }
    let report = Report::new(&cli.budgets, runs, samples);
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
