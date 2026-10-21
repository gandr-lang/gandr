//! `coverage-guard`: the nightly upload of `main`'s coverage against the
//! upload before it.
//!
//! `coverage-guard --repository OWNER/NAME --sha SHA --threshold POINTS
//! [--wait SECONDS] [--file-issue]` waits for Codecov to process the upload
//! of `SHA`, compares it with the processed upload of `main` before it,
//! prints the Markdown report, and with `--file-issue` opens or updates the
//! one drop issue when the coverage fell by more than `POINTS` or the upload
//! covers fewer files.
//!
//! # Exit codes
//!
//! - `0`: the report was printed and filed, whatever it found; also `--help`
//!   and `--version`.
//! - `2`: a refusal — a malformed argument, a failed request or `gh`
//!   invocation, an upload not processed in time, no baseline, or standard
//!   output closed; also a malformed invocation.

use std::io::Write as _;
use std::process::ExitCode;

use anodized::spec;
use gandr_workflow_coverage_guard::CommitSha;
use gandr_workflow_coverage_guard::Comparison;
use gandr_workflow_coverage_guard::GuardError;
use gandr_workflow_coverage_guard::Points;
use gandr_workflow_coverage_guard::Repository;
use gandr_workflow_coverage_guard::Wait;
use gandr_workflow_coverage_guard::codecov;
use gandr_workflow_coverage_guard::github;

/// The exit code of a refusal or a malformed invocation.
const REFUSED: u8 = 2;

/// Main's coverage upload against the one before it.
#[derive(Debug, clap::Parser)]
#[command(name = "coverage-guard", version, about)]
struct Cli
{
    /// The repository, `OWNER/NAME`.
    #[arg(long, env = "GITHUB_REPOSITORY")]
    repository: Repository,
    /// The commit of `main` whose upload is compared.
    #[arg(long, env = "GITHUB_SHA")]
    sha: CommitSha,
    /// The percentage points the coverage may fall before the issue is
    /// filed: `codecov.yml`'s project threshold.
    #[arg(long)]
    threshold: Points,
    /// How many seconds to wait for Codecov to finish processing the upload.
    #[arg(long, default_value = "900")]
    wait: Wait,
    /// Open or update the one drop issue when the coverage dropped.
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
/// - hypothesis: L3 — a drop filed, a steady upload, a failing request, a
///   failing `gh` and a malformed threshold; a swapped stream or exit code
///   changes the observed process result.
/// - witness: `tests::cli::a_drop_opens_the_issue`
/// - witness: `tests::cli::a_failing_request_is_reported_with_its_address`
/// - witness: `tests::cli::a_malformed_threshold_exits_two`
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
        Err(error) => match writeln!(std::io::stderr(), "coverage-guard: {error}") {
            Ok(()) | Err(_) => ExitCode::from(REFUSED),
        },
    }
}

/// Reads both uploads, prints the comparison and files it.
///
/// # Specification
/// - requires: `curl` on the path; with `--file-issue`, `gh` on the path,
///   authenticated for the repository.
/// - ensures: standard output receives the report, then, with `--file-issue`,
///   one line naming what filing did.
/// - provides: the whole command.
/// - fails: every refusal of [`codecov::upload`], [`codecov::previous`],
///   [`codecov::files`] and [`github::file`]; [`GuardError::Output`] when
///   standard output cannot be written.
/// - panics: none.
/// - executable: none — the outcome is the bytes on standard output and the
///   repository's issue.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — as [`main`].
/// - witness: `tests::cli::a_drop_opens_the_issue`
/// - witness: `tests::cli::a_steady_upload_files_nothing`
fn run(cli: Cli) -> Result<(), GuardError>
{
    let after = codecov::upload(&cli.repository, &cli.sha, cli.wait)?;
    let before = codecov::previous(&cli.repository, &cli.sha)?;
    let after_files = codecov::files(&cli.repository, &after.sha)?;
    let before_files = codecov::files(&cli.repository, &before.sha)?;
    let comparison = Comparison::new(
        cli.repository,
        before,
        before_files,
        after,
        after_files,
        cli.threshold,
    );
    let output = |error: std::io::Error| GuardError::Output {
        message: error.to_string(),
    };
    write!(std::io::stdout(), "{comparison}").map_err(output)?;
    if cli.file_issue {
        let filed = github::file(&comparison)?;
        writeln!(std::io::stdout(), "\n{filed}").map_err(output)?;
    }
    Ok(())
}
