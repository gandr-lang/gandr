//! `test-timing`: proposes nextest priority levels from the durations of
//! recent merge-queue runs, or of the one run whose report a target directory
//! keeps.
//!
//! It fetches the JUnit reports of the latest successful merge-queue runs
//! with `gh`, keeping each run in a store so it is fetched once, and prints
//! the tests that have or would have a priority, then the overrides that
//! would set the proposed ones. With `--junit` it reads one report and no
//! store; with `--write` it writes the overrides to a nextest tool
//! configuration, which the next run names, in place of the report.
//!
//! # Exit codes
//!
//! - `0`: the report printed; also `--help` and `--version`.
//! - `2`: a refusal — `gh` failed, the store, a report or the configuration
//!   could not be read, the store held no run, or the output could not be
//!   written; also a malformed invocation.

extern crate alloc;
use alloc::alloc::Global;
use std::io::Write as _;
use std::path::PathBuf;
use std::process::ExitCode;

use anodized::spec;
use gandr_kernel_data::SmallVec;
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
use gandr_workflow_test_timing::read_report;
use gandr_workflow_test_timing::read_run;
use gandr_workflow_test_timing::recent_runs;
use gandr_workflow_test_timing::stored_runs;

/// The small string of `text`. The allocator holds it, or the call panics.
macro_rules! held {
    ($text:expr) => {
        gandr_kernel_data::SmallString::try_from($text).expect("the allocator holds the text")
    };
}

/// The exit code of a refusal or a malformed invocation.
const REFUSED: u8 = 2;
/// The repository name clap parses. Clap builds a `String`.
#[cfg_attr(
    all(dylint_lib = "quenchant_dylints", not(test)),
    expect(
        std_container,
        reason = "clap builds a String. The lint reads a field after #8206"
    )
)]
type ParsedName = String;

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
    repo: ParsedName,
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
    /// Print each test's time instead of the proposal: one tab-separated
    /// `lane binary test seconds` line per test, its lower median in the lane
    /// it held longest.
    #[arg(long)]
    times: bool,
    /// Read this JUnit report of one run in place of the store, with no `gh`:
    /// the report that a target directory keeps of its last run,
    /// `target/nextest/default/junit.xml`.
    #[arg(long)]
    junit: Option<PathBuf>,
    /// Write the proposed priority overrides to this file in place of the
    /// report: a nextest tool configuration, which a run names with
    /// `--tool-config-file test-timing:<file>`.
    #[arg(long)]
    write: Option<PathBuf>,
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
/// - witness: `tests::cli::a_report_reads_the_newest_stored_runs`
/// - witness: `tests::cli::an_empty_store_is_refused`
/// - witness: `tests::cli::a_failing_gh_is_reported_with_its_message`
/// - witness: `tests::cli::a_malformed_invocation_exits_two`
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
    match report(cli) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => match writeln!(std::io::stderr(), "test-timing: {error}") {
            Ok(()) | Err(_) => ExitCode::from(REFUSED),
        },
    }
}

/// Fetches the runs `cli` names, or reads the one report `--junit` names, and
/// prints the proposal, or with `--times` each test's time, or with `--write`
/// writes the proposed overrides.
///
/// # Specification
/// - requires: nothing.
/// - ensures: with `--junit`, that report alone is read, and no store and no
///   `gh`; otherwise, unless `--offline`, every run `gh` lists is in the store,
///   and the newest `--runs` stored runs are read; with `--times` standard
///   output receives one tab-separated `lane binary test seconds` line per
///   test, in test order, and the configuration is not read; with `--write` the
///   file receives the generated overrides as a nextest tool configuration, and
///   standard output receives nothing; otherwise standard output receives the
///   run identifiers, the table and the generated overrides.
/// - provides: the whole report, the times `ci:slow-file` files from, and the
///   priorities of the next run.
/// - fails: every refusal of [`recent_runs`], [`download`], [`stored_runs`],
///   [`read_run`], [`read_report`] and [`Overrides::parse`];
///   [`TimingError::NoRuns`] when the store holds no run; [`TimingError::Io`]
///   when the configuration cannot be read or the file of `--write` cannot be
///   written; [`TimingError::Output`] when standard output cannot be written.
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
///   reads the runs it lists; an empty store is refused; `--times` over one run
///   prints each test by its slowest lane, with no configuration present; one
///   kept report writes the overrides of its slow tests to a file.
/// - witness: `tests::cli::a_report_reads_the_newest_stored_runs`
/// - witness: `tests::cli::fetched_runs_are_stored_and_read_back`
/// - witness: `tests::cli::an_empty_store_is_refused`
/// - witness: `tests::cli::times_print_each_test_by_its_slowest_lane`
/// - witness: `tests::cli::a_kept_report_writes_the_priorities_of_the_next_run`
///
/// # Cost
/// - allocation: the report text and the fetched run list, growth within the
///   stored runs
fn report(cli: Cli) -> Result<(), TimingError>
{
    let mut history = History::default();
    let runs: SmallVec<RunId, 0, Global> = if let Some(ref report) = cli.junit {
        read_report(report, &mut history)?;
        SmallVec::<_, 0, Global>::new()
    }
    else {
        let repository = Repository::from(held!(cli.repo.as_str()));
        if !cli.offline {
            for run in recent_runs(&repository, cli.runs)? {
                download(&repository, run, &cli.store)?;
            }
        }
        let runs: SmallVec<RunId, 0, Global> = stored_runs(&cli.store)?
            .into_iter()
            .take(cli.runs.into())
            .collect();
        if runs.is_empty() {
            return Err(TimingError::NoRuns { dir: cli.store });
        }
        for &run in &runs {
            read_run(&cli.store, run, &mut history)?;
        }
        runs
    };
    let output = |error: std::io::Error| {
        #[cfg_attr(
            all(dylint_lib = "quenchant_dylints", not(test)),
            expect(
                std_container,
                reason = "the call builds a String of alloc, and no local format stands"
            )
        )]
        let built = error.to_string();
        TimingError::Output {
            message: held!(built.as_str()),
        }
    };
    if cli.times {
        let mut stdout = std::io::stdout().lock();
        for (test, timing) in history.timings() {
            writeln!(
                stdout,
                "{}\t{}\t{test}\t{:.3}",
                timing.lane,
                timing.binary,
                timing.median.as_secs_f64()
            )
            .map_err(output)?;
        }
        return stdout.flush().map_err(output);
    }
    let text = std::fs::read_to_string(&cli.config).map_err(|error| TimingError::Io {
        path: cli.config.clone(),
        message: {
            #[cfg_attr(
                all(dylint_lib = "quenchant_dylints", not(test)),
                expect(
                    std_container,
                    reason = "the call builds a String of alloc, and no local format stands"
                )
            )]
            let built = error.to_string();
            held!(built.as_str())
        },
    })?;
    let overrides = Overrides::parse(ConfigText::from(text.as_str()), &cli.config)?;
    let rows = proposals(history.timings(), &overrides);
    if let Some(ref path) = cli.write {
        #[cfg_attr(
            all(dylint_lib = "quenchant_dylints", not(test)),
            expect(
                std_container,
                reason = "the call builds a String of alloc, and no local format stands"
            )
        )]
        let generated = format!(
            "# The priorities of the slowest tests, from the times of the last run.\n\
             # `test-timing --write` writes this file; a run names it with\n\
             # `--tool-config-file test-timing:<file>`.\n\n{}",
            Generated(&rows)
        );
        return std::fs::write(path, generated).map_err(|error| TimingError::Io {
            path: path.clone(),
            message: {
                #[cfg_attr(
                    all(dylint_lib = "quenchant_dylints", not(test)),
                    expect(
                        std_container,
                        reason = "the call builds a String of alloc, and no local format stands"
                    )
                )]
                let built = error.to_string();
                held!(built.as_str())
            },
        });
    }
    #[cfg_attr(
        all(dylint_lib = "quenchant_dylints", not(test)),
        expect(
            std_container,
            reason = "the call builds a String of alloc, and no local format stands"
        )
    )]
    let listed = runs
        .iter()
        .map(ToString::to_string)
        .collect::<SmallVec<_, 0, Global>>()
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
    .map_err(output)
}
