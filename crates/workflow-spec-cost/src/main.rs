//! `spec-cost`: ranks executable specifications by the time the slowest
//! enforcing tests spend checking them.
//!
//! It profiles each test under `perf`, charges every sample to the outermost
//! specification check on its stack, and prints each test's share of checking
//! and the checks by charged time. Run it from the workspace root; Linux only.
//!
//! # Exit codes
//!
//! - `0`: the ranking printed; also `--help` and `--version`.
//! - `2`: a refusal — the store named no test, a source file, the build, the
//!   test list, a profile or the output failed, or a named test does not exist;
//!   also a malformed invocation.

use std::io::Write as _;
use std::path::PathBuf;
use std::process::ExitCode;

use anodized::spec;
use gandr_workflow_spec_cost::CostError;
use gandr_workflow_spec_cost::Frequency;
use gandr_workflow_spec_cost::Ledger;
use gandr_workflow_spec_cost::RankLimit;
use gandr_workflow_spec_cost::Ranking;
use gandr_workflow_spec_cost::Regions;
use gandr_workflow_spec_cost::Suites;
use gandr_workflow_spec_cost::Workload;
use gandr_workflow_spec_cost::WorkloadCount;
use gandr_workflow_spec_cost::read_samples;
use gandr_workflow_spec_cost::record;
use gandr_workflow_spec_cost::slowest_enforcing;
use gandr_workflow_test_timing::RunLimit;

/// The exit code of a refusal or a malformed invocation.
const REFUSED: u8 = 2;

/// Ranks executable specifications by the time the slowest enforcing tests
/// spend checking them.
#[derive(Debug, clap::Parser)]
#[command(name = "spec-cost", version, about)]
struct Cli
{
    /// Profile this many of the slowest enforcing tests the stored runs name.
    #[arg(long, default_value = "5")]
    tests: WorkloadCount,
    /// Read this many of the newest stored runs.
    #[arg(long, default_value = "5")]
    runs: RunLimit,
    /// The store `mise run ci:timing` fills, one directory per run.
    #[arg(long, default_value = "target/test-timing")]
    store: PathBuf,
    /// Profile this test instead, written `BINARY TEST` as nextest prints it;
    /// repeatable.
    #[arg(long = "test", value_name = "BINARY TEST")]
    named: Vec<Workload>,
    /// Samples per second.
    #[arg(long, default_value = "499")]
    frequency: Frequency,
    /// List this many checks.
    #[arg(long, default_value = "30")]
    top: RankLimit,
}

/// Parses the invocation, prints the ranking and chooses the exit code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: exits `0` after printing the ranking, help or version; exits `2`
///   after printing a refusal or a usage message to standard error.
/// - provides: the process boundary.
/// - fails: never; every refusal is an exit code.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a profile through fake tools, an unknown test, an empty
///   store, a failing profile and a zero count; a swapped stream or exit code
///   changes the observed process result.
/// - witness: `cli::cli::a_profile_is_charged_to_its_outermost_specification`
/// - witness: `cli::cli::an_unknown_test_is_refused_by_name`
/// - witness: `cli::cli::an_empty_store_names_nothing_to_profile`
/// - witness: `cli::cli::a_malformed_invocation_exits_two`
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
    match rank(cli) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => match writeln!(std::io::stderr(), "spec-cost: {error}") {
            Ok(()) | Err(_) => ExitCode::from(REFUSED),
        },
    }
}

/// Profiles the tests `cli` names and prints the ranking.
///
/// # Specification
/// - requires: run from the workspace root, with `cargo nextest` and `perf` on
///   the path.
/// - ensures: every named test, or the slowest enforcing tests of the store, is
///   built, profiled once into `target/spec-cost/profiles` and charged;
///   standard output receives the ranking; standard error the progress.
/// - provides: the whole ranking.
/// - fails: every refusal of [`slowest_enforcing`], [`Regions::scan`],
///   [`Suites::build`], [`Suites::get`], [`record`] and [`read_samples`];
///   [`CostError::Io`] when the working directory or the profile directory
///   cannot be had; [`CostError::Output`] when an output stream cannot be
///   written.
/// - panics: none.
/// - executable: none — the outcome is the profiles on disk and the bytes on
///   the output streams, neither observable from the call.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a profile through a fake `cargo` and `perf` prints the
///   asserted ranking; an unknown test and an empty store are refused.
/// - witness: `cli::cli::a_profile_is_charged_to_its_outermost_specification`
/// - witness: `cli::cli::an_unknown_test_is_refused_by_name`
/// - witness: `cli::cli::an_empty_store_names_nothing_to_profile`
fn rank(cli: Cli) -> Result<(), CostError>
{
    let root = std::env::current_dir().map_err(|error| CostError::Io {
        path: PathBuf::from("."),
        message: error.to_string(),
    })?;
    let workloads = if cli.named.is_empty() {
        slowest_enforcing(&cli.store, cli.runs, cli.tests)?
    }
    else {
        cli.named
    };
    let regions = Regions::scan(&root)?;
    let mut progress = std::io::stderr().lock();
    let mut note = |line: core::fmt::Arguments<'_>| {
        writeln!(progress, "spec-cost: {line}").map_err(|error| CostError::Output {
            message: error.to_string(),
        })
    };
    note(format_args!("building the test binaries for sampling"))?;
    let suites = Suites::build(&workloads, &root)?;
    let profiles = root.join("target").join("spec-cost").join("profiles");
    std::fs::create_dir_all(&profiles).map_err(|error| CostError::Io {
        path: profiles.clone(),
        message: error.to_string(),
    })?;
    let mut ledger = Ledger::default();
    for (index, workload) in workloads.iter().enumerate() {
        let suite = suites.get(workload)?;
        let data = profiles.join(format!("{index}.data"));
        note(format_args!("profiling {workload}"))?;
        record(suite, workload, cli.frequency, &data)?;
        read_samples(&data, &root, &regions, workload, &mut ledger)?;
    }
    let mut stdout = std::io::stdout().lock();
    write!(stdout, "{}", Ranking {
        ledger: &ledger,
        frequency: cli.frequency,
        root: &root,
        top: cli.top,
    })
    .and_then(|()| stdout.flush())
    .map_err(|error| CostError::Output {
        message: error.to_string(),
    })
}
