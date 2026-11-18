//! `coverage-guard`: the nightly upload of `main`'s coverage against the
//! upload before it.
//!
//! `coverage-guard --repository OWNER/NAME --sha SHA --threshold POINTS
//! [--wait SECONDS] [--file-issue]` waits for Codecov to process the upload
//! of `SHA`, compares it with the processed upload of `main` before it,
//! prints the Markdown report, and with `--file-issue` opens or updates the
//! one drop issue when the coverage fell by more than `POINTS` or the upload
//! covers fewer files. An upload Codecov leaves unprocessed is named on the
//! report and skipped: the newest processed upload stands in its place, and
//! with `--file-issue` two or more in a row open or update one issue.
//!
//! # Exit codes
//!
//! - `0`: the report was printed and filed, whatever it found; also `--help`
//!   and `--version`.
//! - `2`: a refusal — a malformed argument, a failed request or `gh`
//!   invocation, no processed upload to compare, or standard output closed;
//!   also a malformed invocation.

use std::io::Write as _;
use std::process::ExitCode;

use anodized::spec;
use gandr_workflow_coverage_guard::Badge;
use gandr_workflow_coverage_guard::CommitSha;
use gandr_workflow_coverage_guard::Comparison;
use gandr_workflow_coverage_guard::GuardError;
use gandr_workflow_coverage_guard::Points;
use gandr_workflow_coverage_guard::Repository;
use gandr_workflow_coverage_guard::Unprocessed;
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
    /// Write the README's badge, the newest processed upload as shields.io
    /// endpoint JSON, to this file.
    #[arg(long)]
    badge: Option<std::path::PathBuf>,
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
/// - ensures: standard output receives one line per unprocessed upload skipped,
///   then the report, then, with `--file-issue`, one line naming what filing
///   the unprocessed uploads did when they were filed, and one naming what
///   filing the comparison did.
/// - provides: the whole command.
/// - fails: every refusal of [`codecov::upload`] but
///   [`GuardError::Unprocessed`], and every refusal of [`codecov::newest`],
///   [`codecov::previous`], [`codecov::files`], [`github::file`] and
///   [`github::file_unprocessed`]; [`GuardError::Output`] when standard output
///   cannot be written.
/// - panics: none.
/// - executable: none — the outcome is the bytes on standard output and the
///   repository's issue.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — as [`main`], and a pending head above one and above two
///   unprocessed uploads; refusing the head, or comparing it, changes the
///   observed result.
/// - witness: `tests::cli::a_drop_opens_the_issue`
/// - witness: `tests::cli::a_steady_upload_files_nothing`
/// - witness: `tests::cli::a_pending_head_is_skipped_for_the_newest_processed_upload_3978`
/// - witness: `tests::cli::two_unprocessed_uploads_in_a_row_open_their_issue`
fn run(cli: Cli) -> Result<(), GuardError>
{
    let output = |error: std::io::Error| GuardError::Output {
        message: error.to_string(),
    };
    let (after, skipped) = match codecov::upload(&cli.repository, &cli.sha, cli.wait) {
        Ok(after) => (after, Vec::new()),
        Err(GuardError::Unprocessed { .. }) => {
            let newest = codecov::newest(&cli.repository, &cli.sha)?;
            (newest.upload, newest.skipped)
        },
        Err(error) => return Err(error),
    };
    for upload in &skipped {
        writeln!(std::io::stdout(), "{upload}\n").map_err(output)?;
    }
    if let Some(ref path) = cli.badge {
        std::fs::write(path, Badge::of(&after).to_string()).map_err(|error| GuardError::Badge {
            path: path.display().to_string(),
            message: error.to_string(),
        })?;
    }
    let unprocessed = Unprocessed::filed(&skipped, &after.sha);
    let before = codecov::previous(&cli.repository, &after.sha)?;
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
    write!(std::io::stdout(), "{comparison}").map_err(output)?;
    if cli.file_issue {
        if let Some(ref unprocessed) = unprocessed {
            let filed = github::file_unprocessed(unprocessed)?;
            writeln!(std::io::stdout(), "\n{filed}").map_err(output)?;
        }
        let filed = github::file(&comparison)?;
        writeln!(std::io::stdout(), "\n{filed}").map_err(output)?;
    }
    Ok(())
}
