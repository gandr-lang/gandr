//! `hotpath-guard`: a commit's failed hotpath checks, filed on each
//! regressed function's issue.
//!
//! `hotpath-guard --repository OWNER/NAME --sha SHA [--file-issue]` reads
//! the commit's `hotpath / <benchmark>` checks and the pull request it
//! heads, prints the report, and with `--file-issue` records each regressed
//! function's row on its issue, marks the pull request's rows of passing
//! benchmarks fixed, and closes or reopens each issue as its rows stand.
//!
//! # Exit codes
//!
//! - `0`: the report was printed and filed, whatever it found; also `--help`
//!   and `--version`.
//! - `2`: a refusal — a malformed argument, a failed `gh` invocation, or
//!   standard output closed; also a malformed invocation.

use std::io::Write as _;
use std::process::ExitCode;

use anodized::spec;
use gandr_workflow_hotpath_guard::CommitSha;
use gandr_workflow_hotpath_guard::GuardError;
use gandr_workflow_hotpath_guard::Report;
use gandr_workflow_hotpath_guard::Repository;
use gandr_workflow_hotpath_guard::github;

/// The exit code of a refusal or a malformed invocation.
const REFUSED: u8 = 2;

/// A commit's failed hotpath checks, filed on each regressed function's issue.
#[derive(Debug, clap::Parser)]
#[command(name = "hotpath-guard", version, about)]
struct Cli
{
    /// The repository, `OWNER/NAME`.
    #[arg(long, env = "GITHUB_REPOSITORY")]
    repository: Repository,
    /// The commit the checks ran on: the check run's head.
    #[arg(long)]
    sha: CommitSha,
    /// Record the run on each regressed function's issue.
    #[arg(long)]
    file_issue: bool,
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
/// - hypothesis: L3 — a failure filed, a clear commit, a failing `gh` and a
///   malformed commit; a swapped stream or exit code changes the observed
///   process result.
/// - witness: `tests::cli::a_failed_check_opens_one_issue_per_function`
/// - witness: `tests::cli::a_failing_gh_is_reported_with_its_message`
/// - witness: `tests::cli::a_malformed_commit_exits_two`
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
        Err(error) => match writeln!(std::io::stderr(), "hotpath-guard: {error}") {
            Ok(()) | Err(_) => ExitCode::from(REFUSED),
        },
    }
}

/// Reads the checks and the pull request, prints the report and files it.
///
/// # Specification
/// - requires: `gh` on the path, authenticated for the repository.
/// - ensures: standard output receives the report, then, with `--file-issue`,
///   one line per issue filing touched, or one line saying none was.
/// - provides: the whole command.
/// - fails: every refusal of [`github::checks`], [`github::pull`] and
///   [`github::file`]; [`GuardError::Output`] when standard output cannot be
///   written.
/// - panics: none.
/// - executable: none — the outcome is the bytes on standard output and the
///   repository's issues.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — as [`main`].
/// - witness: `tests::cli::a_failed_check_opens_one_issue_per_function`
/// - witness: `tests::cli::a_clear_commit_files_nothing`
fn run(cli: Cli) -> Result<(), GuardError>
{
    let checks = github::checks(&cli.repository, &cli.sha)?;
    let pull = github::pull(&cli.repository, &cli.sha)?;
    let report = Report::new(cli.repository, cli.sha, pull, checks);
    let output = |error: std::io::Error| GuardError::Output {
        message: error.to_string(),
    };
    write!(std::io::stdout(), "{report}").map_err(output)?;
    if cli.file_issue {
        let filed = github::file(&report)?;
        if filed.is_empty() {
            writeln!(
                std::io::stdout(),
                "\nNo function regressed and no row was fixed."
            )
            .map_err(output)?;
        }
        for filing in filed {
            writeln!(std::io::stdout(), "\n{filing}").map_err(output)?;
        }
    }
    Ok(())
}
