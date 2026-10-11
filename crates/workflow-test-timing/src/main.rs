//! `test-timing`: proposes nextest priority levels from the durations of
//! recent merge-queue runs.
//!
//! It fetches the JUnit reports of the latest successful merge-queue runs
//! with `gh`, keeping each run in a store so it is fetched once, and prints
//! the tests that have or would have a priority, then the overrides that
//! would set the proposed ones.
//!
//! # Exit codes
//!
//! - `0`: the report printed; also `--help` and `--version`.
//! - `2`: a refusal — `gh` failed, the store, a report or the configuration
//!   could not be read, the store held no run, or the output could not be
//!   written; also a malformed invocation.

use std::io::Write as _;
use std::path::PathBuf;
use std::process::ExitCode;

use anodized::spec;
use gandr_workflow_test_timing::ConfigText;
use gandr_workflow_test_timing::Generated;
use gandr_workflow_test_timing::History;
use gandr_workflow_test_timing::Overrides;
use gandr_workflow_test_timing::Repository;
use gandr_workflow_test_timing::RunId;
use gandr_workflow_test_timing::RunLimit;
use gandr_workflow_test_timing::Table;
use gandr_workflow_test_timing::TimingError;
use gandr_workflow_test_timing::download;
use gandr_workflow_test_timing::proposals;
use gandr_workflow_test_timing::read_run;
use gandr_workflow_test_timing::recent_runs;
use gandr_workflow_test_timing::stored_runs;

/// The exit code of a refusal or a malformed invocation.
const REFUSED: u8 = 2;

/// Proposes nextest priority levels from recent merge-queue runs.
#[derive(Debug, clap::Parser)]
#[command(name = "test-timing", version, about)]
struct Cli
{
    /// Report on this many of the latest successful merge-queue runs.
    #[arg(long, default_value = "5")]
    runs: RunLimit,
    /// The repository the runs belong to, as OWNER/NAME.
    #[arg(long, default_value = "gandr-lang/gandr")]
    repo: String,
    /// The nextest configuration whose priorities the proposal is compared
    /// with.
    #[arg(long, default_value = ".config/nextest.toml")]
    config: PathBuf,
    /// The store of fetched runs, one directory per run.
    #[arg(long, default_value = "target/test-timing")]
    store: PathBuf,
    /// Report on the runs already stored without invoking `gh`.
    #[arg(long)]
    offline: bool,
}

/// Parses the invocation, prints the report and chooses the exit code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: exits `0` after printing the report, help or version; exits `2`
///   after printing a refusal or a usage message to standard error.
/// - provides: the process boundary.
/// - fails: never; every refusal is an exit code.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a stored report, an empty store, a failing `gh`, an
///   unknown flag and `--help`; a swapped stream or exit code changes the
///   observed process result.
/// - witness: `cli::cli::a_report_reads_the_newest_stored_runs`
/// - witness: `cli::cli::an_empty_store_is_refused`
/// - witness: `cli::cli::a_failing_gh_is_reported_with_its_message`
/// - witness: `cli::cli::a_malformed_invocation_exits_two`
#[spec(ensures: |ret| ret == ExitCode::SUCCESS || ret == ExitCode::from(REFUSED))]
fn main() -> ExitCode
{
    let cli = match <Cli as clap::Parser>::try_parse() {
        | Ok(cli) => cli,
        | Err(error) => {
            return match (error.print(), error.use_stderr()) {
                | (Ok(()), false) => ExitCode::SUCCESS,
                | (Ok(()), true) | (Err(_), _) => ExitCode::from(REFUSED),
            };
        },
    };
    match report(cli) {
        | Ok(()) => ExitCode::SUCCESS,
        | Err(error) => match writeln!(std::io::stderr(), "test-timing: {error}") {
            | Ok(()) | Err(_) => ExitCode::from(REFUSED),
        },
    }
}

/// Fetches the runs `cli` names, reads them and prints the proposal.
///
/// # Specification
/// - requires: nothing.
/// - ensures: unless `--offline`, every run `gh` lists is in the store; the
///   newest `--runs` stored runs are read; standard output receives the run
///   identifiers, the table and the generated overrides.
/// - provides: the whole report.
/// - fails: every refusal of [`recent_runs`], [`download`], [`stored_runs`],
///   [`read_run`] and [`Overrides::parse`]; [`TimingError::NoRuns`] when the
///   store holds no run; [`TimingError::Io`] when the configuration cannot be
///   read; [`TimingError::Output`] when standard output cannot be written.
/// - panics: none.
/// - executable: none — the outcome is the store on disk and the bytes on
///   standard output, neither observable from the call.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — the offline report over three stored runs reads only the
///   newest two when asked for two; a fetch through a fake `gh` stores and
///   reads the runs it lists; an empty store is refused.
/// - witness: `cli::cli::a_report_reads_the_newest_stored_runs`
/// - witness: `cli::cli::fetched_runs_are_stored_and_read_back`
/// - witness: `cli::cli::an_empty_store_is_refused`
fn report(cli: Cli) -> Result<(), TimingError>
{
    let repository = Repository::from(cli.repo);
    if !cli.offline {
        for run in recent_runs(&repository, cli.runs)? {
            download(&repository, run, &cli.store)?;
        }
    }
    let runs: Vec<RunId> = stored_runs(&cli.store)?
        .into_iter()
        .take(cli.runs.into())
        .collect();
    if runs.is_empty() {
        return Err(TimingError::NoRuns { dir: cli.store });
    }
    let mut history = History::default();
    for &run in &runs {
        read_run(&cli.store, run, &mut history)?;
    }
    let text = std::fs::read_to_string(&cli.config).map_err(|error| TimingError::Io {
        path: cli.config.clone(),
        message: error.to_string(),
    })?;
    let overrides = Overrides::parse(ConfigText::from(text.as_str()), &cli.config)?;
    let rows = proposals(history.timings(), &overrides);
    let listed = runs
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(", ");
    let mut stdout = std::io::stdout().lock();
    write!(
        stdout,
        "runs: {listed}\n\n{}\n# Proposed priority overrides: these replace the \
         `[[profile.default.overrides]]`\n# tables of {} that set `priority`.\n\n{}",
        Table(&rows),
        cli.config.display(),
        Generated(&rows),
    )
    .and_then(|()| stdout.flush())
    .map_err(|error| TimingError::Output {
        message: error.to_string(),
    })
}
