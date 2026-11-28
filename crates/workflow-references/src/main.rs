//! `references`: judges the citations of a tree against the citation window.
//!
//! | Invocation | Does | Exits `1` when |
//! | --- | --- | --- |
//! | `references window [--root <dir>]` | reads the sources, the work rows of `ledger/references.sql` and `.config/references/window.toml` of the tree, and prints each finding of the window | a finding |
//!
//! With `--cost`, the binary prints each part of the run on standard error,
//! with its count and its time.
//!
//! The binary exits with one of three codes:
//!
//! - `0`: the citations keep the window; also `--help` and `--version`.
//! - `1`: a finding.
//! - `2`: a file that cannot be read, a policy that cannot be read, output that
//!   cannot be written, or a malformed invocation.

use std::path::Path;
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Instant;

use anodized::spec;
use gandr_workflow_references::cites::citations;
use gandr_workflow_references::sources;
use gandr_workflow_references::window::Policy;
use gandr_workflow_references::window::findings;
use gandr_workflow_references::window::works;

/// The exit code of a finding.
const FOUND: u8 = 1;

/// The exit code of a fault or a malformed invocation.
const FAULTED: u8 = 2;

/// Judges the citations of a tree.
#[derive(Debug, clap::Parser)]
#[command(name = "references", version, about)]
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
    /// Refuses each citation of a work older than the cutoff year at a site
    /// that no entry of `.config/references/window.toml` keeps.
    Window
    {
        /// The root of the tree.
        #[arg(long, value_name = "DIR", default_value = ".")]
        root: PathBuf,
        /// Print each part of the run with its count and its time.
        #[arg(long)]
        cost: bool,
    },
}

/// Reads the file `path` below `root`, or writes the fault to `stderr`.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The [`std::io::Error`] of a write to `stderr` that failed.
fn read(
    root: &Path,
    path: &str,
    stderr: &mut impl std::io::Write,
) -> std::io::Result<Option<String>>
{
    match std::fs::read_to_string(root.join(path)) {
        Ok(text) => Ok(Some(text)),
        Err(error) => {
            writeln!(stderr, "references: {path}: cannot read: {error}")?;
            Ok(None)
        },
    }
}

/// Runs the window over the tree at `root`, prints each finding on
/// `stderr`, and chooses the exit code.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The [`std::io::Error`] of the first write to a stream that failed.
///
/// # Cost
/// - allocation: the text of each source and the citations, setup
/// - io: one read of each source and of the two files of the window
fn window(
    root: &Path,
    cost: bool,
    stdout: &mut impl std::io::Write,
    stderr: &mut impl std::io::Write,
) -> std::io::Result<ExitCode>
{
    let start = Instant::now();
    let paths = match sources(root) {
        Ok(paths) => paths,
        Err(error) => {
            writeln!(
                stderr,
                "references: {}: cannot list the sources: {error}",
                root.display()
            )?;
            return Ok(ExitCode::from(FAULTED));
        },
    };
    let mut cites = Vec::new();
    for path in &paths {
        let Some(text) = read(root, path, stderr)?
        else {
            return Ok(ExitCode::from(FAULTED));
        };
        cites.extend(citations(path, &text));
    }
    let read_sources = start.elapsed();
    let start = Instant::now();
    let Some(ledger) = read(root, "ledger/references.sql", stderr)?
    else {
        return Ok(ExitCode::from(FAULTED));
    };
    let Some(policy) = read(root, ".config/references/window.toml", stderr)?
    else {
        return Ok(ExitCode::from(FAULTED));
    };
    let policy = match Policy::read(&policy) {
        Ok(policy) => policy,
        Err(fault) => {
            writeln!(stderr, "references: {fault}")?;
            return Ok(ExitCode::from(FAULTED));
        },
    };
    let works = works(&ledger);
    let found = findings(&cites, &works, &policy);
    let judged = start.elapsed();
    for line in &found {
        writeln!(stderr, "{line}")?;
    }
    if cost {
        writeln!(
            stderr,
            "references: sources: {} files, {} citations, {} µs",
            paths.len(),
            cites.len(),
            read_sources.as_micros()
        )?;
        writeln!(
            stderr,
            "references: window: {} works, {} entries, {} µs",
            works.len(),
            policy.entries(),
            judged.as_micros()
        )?;
    }
    if found.is_empty() {
        writeln!(
            stdout,
            "references window OK: {} sources, the window opens in {}, {} entries keep an older work",
            paths.len(),
            policy.cutoff,
            policy.entries()
        )?;
        Ok(ExitCode::SUCCESS)
    }
    else {
        writeln!(stderr, "references window FAILED: {} findings", found.len())?;
        Ok(ExitCode::from(FOUND))
    }
}

/// Parses the invocation, runs it and chooses the exit code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: exits as [`window`] chooses; exits `2` when a stream cannot be
///   written, and after a usage message on standard error; exits `0` after
///   `--help` or `--version`.
/// - provides: the process boundary.
/// - fails: never; every fault is an exit code.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a tree whose citations keep the window exits zero, and a
///   tree with a new older citation exits one and names its site.
/// - witness: `tests::cli::the_window_reads_the_sources_of_a_tree`
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
    match cli.command {
        Command::Window { root, cost } => window(
            &root,
            cost,
            &mut std::io::stdout().lock(),
            &mut std::io::stderr().lock(),
        ),
    }
    .unwrap_or_else(|_unwritten| ExitCode::from(FAULTED))
}
