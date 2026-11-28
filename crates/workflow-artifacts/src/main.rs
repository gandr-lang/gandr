//! `artifacts`: holds a tree to the list of the files that a program writes.
//!
//! | Invocation | Does | Exits `1` when |
//! | --- | --- | --- |
//! | `artifacts tracked [--root <dir>]` | reads the tracked files and the list, and prints each tracked file of an output or a ratchet | a tracked file of an output or a ratchet, or a `pending` row with no tracked file |
//! | `artifacts clean [--root <dir>]` | reads the status of the checkout, and prints each changed file and each file that git does not know, with the row of the list that holds it | a changed file or an unknown file |
//!
//! The landing runs `tracked` before its gates and `clean` after them. With
//! `--cost`, the binary prints each part of the run on standard error, with
//! its count and its time.
//!
//! The binary exits with one of three codes:
//!
//! - `0`: the tree keeps the list; also `--help` and `--version`.
//! - `1`: a finding.
//! - `2`: a list that cannot be read, a git that fails, output that cannot be
//!   written, or a malformed invocation.

use std::path::Path;
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Instant;

use anodized::spec;
use gandr_workflow_artifacts::LIST;
use gandr_workflow_artifacts::Row;
use gandr_workflow_artifacts::crates;
use gandr_workflow_artifacts::entries;
use gandr_workflow_artifacts::read;
use gandr_workflow_artifacts::tracked;
use gandr_workflow_artifacts::unclean;

/// The exit code of a finding.
const FOUND: u8 = 1;

/// The exit code of a fault or a malformed invocation.
const FAULTED: u8 = 2;

/// Holds a tree to the list of the files that a program writes.
#[derive(Debug, clap::Parser)]
#[command(name = "artifacts", version, about)]
struct Cli
{
    /// What to judge.
    #[command(subcommand)]
    command: Command,
}

/// The judgements of the binary.
#[derive(Debug, clap::Subcommand)]
enum Command
{
    /// Refuses each tracked file below a path of an output or of a ratchet,
    /// and each `pending` row with no tracked file.
    Tracked
    {
        /// The root of the tree.
        #[arg(long, value_name = "DIR", default_value = ".")]
        root: PathBuf,
        /// Print each part of the run with its count and its time.
        #[arg(long)]
        cost: bool,
    },
    /// Refuses each changed file and each file that git does not know and
    /// does not ignore.
    Clean
    {
        /// The root of the tree.
        #[arg(long, value_name = "DIR", default_value = ".")]
        root: PathBuf,
        /// Print each part of the run with its count and its time.
        #[arg(long)]
        cost: bool,
    },
}

/// The rows of the list and the crates of the tree at `root`, or the fault
/// on `stderr`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The [`std::io::Error`] of a write to `stderr` that failed.
fn list(
    root: &Path,
    stderr: &mut impl std::io::Write,
) -> std::io::Result<Option<(Vec<Row>, Vec<String>)>>
{
    let text = match std::fs::read_to_string(root.join(LIST)) {
        Ok(text) => text,
        Err(error) => {
            writeln!(stderr, "artifacts: {LIST}: cannot read: {error}")?;
            return Ok(None);
        },
    };
    let rows = match read(&text) {
        Ok(rows) => rows,
        Err(error) => {
            writeln!(stderr, "artifacts: {LIST}: {error}")?;
            return Ok(None);
        },
    };
    match crates(root) {
        Ok(names) => Ok(Some((rows, names))),
        Err(error) => {
            writeln!(stderr, "artifacts: crates: cannot read: {error}")?;
            Ok(None)
        },
    }
}

/// The standard output of `git` with `arguments` in `root`, or the fault on
/// `stderr`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The [`std::io::Error`] of a write to `stderr` that failed.
fn git(
    root: &Path,
    arguments: &[&str],
    stderr: &mut impl std::io::Write,
) -> std::io::Result<Option<Vec<u8>>>
{
    match std::process::Command::new("git")
        .arg("-C")
        .arg(root)
        .args(arguments)
        .output()
    {
        Ok(output) if output.status.success() => Ok(Some(output.stdout)),
        Ok(output) => {
            writeln!(
                stderr,
                "artifacts: git {}: {}",
                arguments.join(" "),
                String::from_utf8_lossy(&output.stderr).trim_end()
            )?;
            Ok(None)
        },
        Err(error) => {
            writeln!(stderr, "artifacts: git: cannot start: {error}")?;
            Ok(None)
        },
    }
}

/// Runs `tracked` over the tree at `root`, prints each finding on `stderr`,
/// and chooses the exit code.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The [`std::io::Error`] of the first write to a stream that failed.
///
/// # Cost
/// - allocation: the paths of the tracked files, setup
/// - io: one run of `git ls-files`, one read of the list and of `crates/`
fn run_tracked(
    root: &Path,
    cost: bool,
    stdout: &mut impl std::io::Write,
    stderr: &mut impl std::io::Write,
) -> std::io::Result<ExitCode>
{
    let start = Instant::now();
    let Some((rows, names)) = list(root, stderr)?
    else {
        return Ok(ExitCode::from(FAULTED));
    };
    let Some(listed) = git(root, &["ls-files", "-z"], stderr)?
    else {
        return Ok(ExitCode::from(FAULTED));
    };
    let mut files: Vec<String> = listed
        .split(|&byte| byte == 0)
        .filter(|path| !path.is_empty())
        .map(|path| String::from_utf8_lossy(path).into_owned())
        .collect();
    files.sort_unstable();
    let read_tree = start.elapsed();
    let start = Instant::now();
    let found = tracked(&rows, &names, &files);
    let judged = start.elapsed();
    for finding in &found {
        writeln!(stderr, "{finding}")?;
    }
    if cost {
        writeln!(
            stderr,
            "artifacts: tree: {} files, {} rows, {} crates, {} µs",
            files.len(),
            rows.len(),
            names.len(),
            read_tree.as_micros()
        )?;
        writeln!(
            stderr,
            "artifacts: tracked: {} findings, {} µs",
            found.len(),
            judged.as_micros()
        )?;
    }
    if found.is_empty() {
        let pending = rows.iter().filter(|row| row.pending.is_some()).count();
        writeln!(
            stdout,
            "artifacts tracked OK: {} tracked files, no file of an output or a ratchet but the {pending} rows that wait for their unit",
            files.len()
        )?;
        Ok(ExitCode::SUCCESS)
    }
    else {
        writeln!(stderr, "artifacts tracked FAILED: {} findings", found.len())?;
        Ok(ExitCode::from(FOUND))
    }
}

/// Runs `clean` over the checkout at `root`, prints each finding on
/// `stderr`, and chooses the exit code.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The [`std::io::Error`] of the first write to a stream that failed.
///
/// # Cost
/// - allocation: the entries of the status
/// - io: one run of `git status`, one read of the list and of `crates/`
fn run_clean(
    root: &Path,
    cost: bool,
    stdout: &mut impl std::io::Write,
    stderr: &mut impl std::io::Write,
) -> std::io::Result<ExitCode>
{
    let start = Instant::now();
    let Some((rows, names)) = list(root, stderr)?
    else {
        return Ok(ExitCode::from(FAULTED));
    };
    let Some(status) = git(
        root,
        &["status", "--porcelain=v1", "-z", "--untracked-files=all"],
        stderr,
    )?
    else {
        return Ok(ExitCode::from(FAULTED));
    };
    let found = unclean(&rows, &names, &entries(&status));
    let judged = start.elapsed();
    for finding in &found {
        writeln!(stderr, "{finding}")?;
    }
    if cost {
        writeln!(
            stderr,
            "artifacts: clean: {} findings, {} µs",
            found.len(),
            judged.as_micros()
        )?;
    }
    if found.is_empty() {
        writeln!(
            stdout,
            "artifacts clean OK: the checkout has no changed file and no file that git does not know"
        )?;
        Ok(ExitCode::SUCCESS)
    }
    else {
        writeln!(stderr, "artifacts clean FAILED: {} findings", found.len())?;
        Ok(ExitCode::from(FOUND))
    }
}

/// Parses the invocation, runs it and chooses the exit code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: exits as [`run_tracked`] or [`run_clean`] chooses; exits `2` when
///   a stream cannot be written, and after a usage message on standard error;
///   exits `0` after `--help` or `--version`.
/// - provides: the process boundary.
/// - fails: never; every fault is an exit code.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a tree that keeps the list exits zero for each command,
///   and a tracked output or a file that a run wrote exits one and names its
///   path.
/// - witness: `tests::cli::the_gate_refuses_a_tracked_output_and_an_unclean_checkout`
#[spec(ensures: |ret| ret == ExitCode::SUCCESS || ret == ExitCode::from(FOUND) || ret == ExitCode::from(FAULTED))]
fn main() -> ExitCode
{
    let cli = match <Cli as clap::Parser>::try_parse() {
        Ok(cli) => cli,
        Err(error) => {
            let code = if error.use_stderr() {
                ExitCode::from(FAULTED)
            }
            else {
                ExitCode::SUCCESS
            };
            return match error.print() {
                Ok(()) => code,
                Err(_unwritten) => ExitCode::from(FAULTED),
            };
        },
    };
    let stdout = &mut std::io::stdout().lock();
    let stderr = &mut std::io::stderr().lock();
    match cli.command {
        Command::Tracked { root, cost } => run_tracked(&root, cost, stdout, stderr),
        Command::Clean { root, cost } => run_clean(&root, cost, stdout, stderr),
    }
    .unwrap_or_else(|_unwritten| ExitCode::from(FAULTED))
}
