//! `hotpath-judge`: a commit's runs of one benchmark judged against its
//! base's, written as a `hotpath / <benchmark>` check.
//!
//! `hotpath-judge --repository OWNER/NAME --head SHA --base SHA --benchmark
//! NAME --policy FILE --base-run FILE… --head-run FILE… [--band] --output
//! FILE` reads each run's JSON report and the policy, judges the rows
//! ([`gandr_workflow_hotpath_guard::judge`]), prints the summary, and writes
//! the check run's body — its name, conclusion, title and summary — as JSON
//! to the output file. `--band` judges only the rows under the policy's
//! share floor: hotpath Cloud judges the rest of a pull request.
//!
//! # Exit codes
//!
//! - `0`: the judgement was written, whatever it found; also `--help` and
//!   `--version`.
//! - `2`: a refusal — an unreadable or malformed report or policy, an
//!   unwritable output, a malformed argument; also a malformed invocation.

use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::process::ExitCode;

use anodized::spec;
use gandr_workflow_hotpath_guard::CommitSha;
use gandr_workflow_hotpath_guard::GuardError;
use gandr_workflow_hotpath_guard::Repository;
use gandr_workflow_hotpath_guard::judge;

/// The exit code of a refusal or a malformed invocation.
const REFUSED: u8 = 2;

/// A commit's runs of one benchmark judged against its base's.
#[derive(Debug, clap::Parser)]
#[command(name = "hotpath-judge", version, about)]
struct Cli
{
    /// The repository, `OWNER/NAME`.
    #[arg(long, env = "GITHUB_REPOSITORY")]
    repository: Repository,
    /// The commit judged.
    #[arg(long)]
    head: CommitSha,
    /// The commit it is judged against.
    #[arg(long)]
    base: CommitSha,
    /// The check's benchmark: `hotpath / <benchmark>`.
    #[arg(long)]
    benchmark: String,
    /// The benchmark's regression policy.
    #[arg(long)]
    policy: PathBuf,
    /// A report of the base's runs; one per run.
    #[arg(long = "base-run", required = true)]
    base_runs: Vec<PathBuf>,
    /// A report of the commit's runs; one per run.
    #[arg(long = "head-run", required = true)]
    head_runs: Vec<PathBuf>,
    /// Judge only the rows under the policy's share floor.
    #[arg(long)]
    band: bool,
    /// Where the check run's body is written.
    #[arg(long)]
    output: PathBuf,
}

/// Parses the invocation, judges and chooses the exit code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: exits `0` after writing the judgement, help or version; exits `2`
///   after printing a refusal or a usage message to standard error.
/// - provides: the process boundary.
/// - fails: never; every refusal is an exit code.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a regressed band, a clear one and a missing report; a
///   swapped stream, conclusion or exit code changes the observed result.
/// - witness: `tests::judge::a_regressed_band_writes_a_failed_check`
/// - witness: `tests::judge::a_missing_report_exits_two`
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
    match run(&cli) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => match writeln!(std::io::stderr(), "hotpath-judge: {error}") {
            Ok(()) | Err(_) => ExitCode::from(REFUSED),
        },
    }
}

/// A file named on the command line, its path as a refusal names it and its
/// text.
#[derive(Debug)]
struct File
{
    /// The path, as given.
    path: String,
    /// The file's text.
    text: String,
}

impl File
{
    /// Reads the file.
    ///
    /// # Specification
    /// - requires: nothing.
    /// - ensures: the path as given and the file's text.
    /// - provides: every input the judgement reads.
    /// - fails: [`GuardError::Input`] naming the path when it cannot be read.
    /// - panics: none.
    /// - executable: none — the outcome is the file on disk.
    ///
    /// # Errors
    /// As `fails` lists.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`main`].
    /// - witness: `tests::judge::a_missing_report_exits_two`
    fn read(path: &Path) -> Result<Self, GuardError>
    {
        let shown = path.display().to_string();
        match std::fs::read_to_string(path) {
            Ok(text) => Ok(Self { path: shown, text }),
            Err(error) => Err(GuardError::Input {
                path: shown,
                message: error.to_string(),
            }),
        }
    }

    /// The file as the judge reads it.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — as [`main`].
    /// - witness: `tests::judge::a_regressed_band_writes_a_failed_check`
    fn input(&self) -> judge::Input<'_>
    {
        judge::Input {
            path: &self.path,
            text: &self.text,
        }
    }
}

/// Reads the inputs, judges, prints the summary and writes the check.
///
/// # Specification
/// - requires: nothing.
/// - ensures: standard output receives the summary; the output file holds
///   `{"name": "hotpath / <benchmark>", "conclusion": "failure" | "success",
///   "output": {"title", "summary"}}`, a failure exactly when a row regressed.
/// - provides: the whole command.
/// - fails: every refusal of [`File::read`], [`judge::Run::read`] and
///   [`judge::Policy::read`]; [`GuardError::Input`] when the output cannot be
///   written; [`GuardError::Output`] when standard output cannot be.
/// - panics: none.
/// - executable: none — the outcome is the bytes written.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — as [`main`].
/// - witness: `tests::judge::a_regressed_band_writes_a_failed_check`
/// - witness: `tests::judge::a_clear_band_writes_a_passed_check`
fn run(cli: &Cli) -> Result<(), GuardError>
{
    let policy = judge::Policy::read(File::read(&cli.policy)?.input())?;
    let runs = |paths: &[PathBuf]| {
        paths
            .iter()
            .map(|path| judge::Run::read(File::read(path)?.input()))
            .collect::<Result<Vec<_>, _>>()
    };
    let scope = if cli.band {
        judge::Scope::Band
    }
    else {
        judge::Scope::All
    };
    let verdict = judge::judge(
        &policy,
        scope,
        &runs(&cli.base_runs)?,
        &runs(&cli.head_runs)?,
    );
    let summary = judge::Summary {
        subject: judge::Subject {
            repository: &cli.repository,
            head: &cli.head,
            base: &cli.base,
            benchmark: &cli.benchmark,
        },
        verdict: &verdict,
    }
    .to_string();
    write!(std::io::stdout(), "{summary}").map_err(|error| GuardError::Output {
        message: error.to_string(),
    })?;
    let conclusion = verdict.conclusion();
    let title = match conclusion {
        judge::Conclusion::Failure => "a row regressed past its policy",
        judge::Conclusion::Success => "no row regressed past its policy",
    };
    let body = serde_json::json!({
        "name": format!("hotpath / {}", cli.benchmark),
        "conclusion": conclusion.to_string(),
        "output": {"title": title, "summary": summary},
    });
    std::fs::write(&cli.output, body.to_string()).map_err(|error| GuardError::Input {
        path: cli.output.display().to_string(),
        message: error.to_string(),
    })
}
