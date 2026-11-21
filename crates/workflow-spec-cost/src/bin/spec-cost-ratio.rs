//! `spec-cost-ratio`: each test's enforcing time over its plain time, from two
//! nextest JUnit reports, as Markdown for a CI job summary.
//!
//! # Exit codes
//!
//! - `0`: the comparison printed, flagged tests or none; also `--help` and
//!   `--version`.
//! - `2`: a refusal — a report could not be read or is not one nextest wrote,
//!   or the output failed; also a malformed invocation.

use std::io::Write as _;
use std::path::PathBuf;
use std::process::ExitCode;

use anodized::spec;
use gandr_workflow_spec_cost::Baseline;
use gandr_workflow_spec_cost::Commit;
use gandr_workflow_spec_cost::Comparisons;
use gandr_workflow_spec_cost::CostError;
use gandr_workflow_spec_cost::Factor;
use gandr_workflow_spec_cost::Floor;
use gandr_workflow_spec_cost::Hours;
use gandr_workflow_spec_cost::RankLimit;
use gandr_workflow_spec_cost::pair;
use gandr_workflow_test_timing::report::ReportText;

/// The exit code of a refusal or a malformed invocation.
const REFUSED: u8 = 2;

/// Compares each test's enforcing time with its plain time, from two nextest
/// JUnit reports.
#[derive(Debug, clap::Parser)]
#[command(name = "spec-cost-ratio", version)]
struct Cli
{
    /// The plain baseline's JUnit report.
    #[arg(long)]
    plain: PathBuf,
    /// The enforcing run's JUnit report.
    #[arg(long)]
    enforcing: PathBuf,
    /// The commit the plain baseline timed.
    #[arg(long)]
    baseline_commit: Commit,
    /// How many whole hours before the enforcing run the baseline ran.
    #[arg(long)]
    baseline_age_hours: Hours,
    /// Flag a test whose ratio reaches this, written with at most two
    /// decimals.
    #[arg(long, default_value = "4")]
    threshold: Factor,
    /// Flag only a test taking at least this many seconds enforcing.
    #[arg(long, default_value = "0.25")]
    floor: Floor,
    /// List this many tests, besides every flagged one.
    #[arg(long, default_value = "20")]
    top: RankLimit,
}

/// Parses the invocation, prints the comparison and chooses the exit code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: exits `0` after printing the comparison, help or version; exits
///   `2` after printing a refusal or a usage message to standard error.
/// - provides: the process boundary.
/// - fails: never; every refusal is an exit code.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a recorded pair, a missing report and a malformed
///   threshold; a swapped stream or exit code changes the observed process
///   result.
/// - witness: `tests::ratio::a_recorded_pair_reports_each_test_against_the_baseline`
/// - witness: `tests::ratio::a_missing_report_is_refused_by_its_path`
/// - witness: `tests::ratio::a_malformed_threshold_exits_two`
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
    match compare(cli) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => match writeln!(std::io::stderr(), "spec-cost-ratio: {error}") {
            Ok(()) | Err(_) => ExitCode::from(REFUSED),
        },
    }
}

/// Reads the two reports `cli` names and prints their comparison.
///
/// # Specification
/// - requires: nothing.
/// - ensures: standard output receives the Markdown comparison of the two
///   reports against the baseline `cli` names.
/// - provides: the whole comparison.
/// - fails: [`CostError::Io`] when a report cannot be read; every refusal of
///   [`pair`]; [`CostError::Output`] when standard output cannot be written.
/// - panics: none.
/// - executable: none — the outcome is the bytes on standard output, not
///   observable from the call.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a recorded pair prints the asserted comparison and a
///   missing report is refused by its path.
/// - witness: `tests::ratio::a_recorded_pair_reports_each_test_against_the_baseline`
/// - witness: `tests::ratio::a_missing_report_is_refused_by_its_path`
fn compare(cli: Cli) -> Result<(), CostError>
{
    let read = |path: &PathBuf| {
        std::fs::read_to_string(path).map_err(|error| CostError::Io {
            path: path.clone(),
            message: error.to_string(),
        })
    };
    let plain = read(&cli.plain)?;
    let enforcing = read(&cli.enforcing)?;
    let pairing = pair(
        ReportText::from(plain.as_str()),
        &cli.plain,
        ReportText::from(enforcing.as_str()),
        &cli.enforcing,
    )?;
    let baseline = Baseline {
        commit: cli.baseline_commit,
        age: cli.baseline_age_hours,
    };
    let mut stdout = std::io::stdout().lock();
    write!(stdout, "{}", Comparisons {
        pairing: &pairing,
        baseline: &baseline,
        threshold: cli.threshold,
        floor: cli.floor,
        top: cli.top,
    })
    .and_then(|()| stdout.flush())
    .map_err(|error| CostError::Output {
        message: error.to_string(),
    })
}
