//! `twin-census`: writes or checks `ledger/twin-census.md`, the census of the
//! crates under the emitter.
//!
//! | Invocation | Does | Exits `1` when |
//! | --- | --- | --- |
//! | `twin-census --write [--root <directory>]` | writes the census and prints its path and its counts | never |
//! | `twin-census --check [--root <directory>]` | compares the committed census with the census of the workspace | the census is stale |
//!
//! With `--cost`, the binary prints each part of the run on standard error,
//! with its count of calls and its time.
//!
//! The binary exits with one of three codes:
//!
//! - `0`: the census is written, or it is the census of the workspace; also
//!   `--help` and `--version`.
//! - `1`: the committed census is stale. Standard error names each row that
//!   differs.
//! - `2`: `cargo metadata` that does not run or does not succeed, metadata that
//!   does not read, a file that cannot be read or written, output that cannot
//!   be written, or a malformed invocation.

use core::time::Duration;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::process::ExitCode;
use std::time::Instant;

use anodized::spec;
use gandr_workflow_twin_census::CENSUS_PATH;
use gandr_workflow_twin_census::CensusError;
use gandr_workflow_twin_census::Workspace;
use gandr_workflow_twin_census::stale;

/// The exit code of a stale census.
const STALE: u8 = 1;

/// The exit code of a fault or a malformed invocation.
const FAULTED: u8 = 2;

/// Writes or checks the census of the crates under the emitter.
#[derive(Debug, clap::Parser)]
#[command(name = "twin-census", version, about)]
struct Cli
{
    /// Write the census.
    #[arg(long, conflicts_with = "check", required_unless_present = "check")]
    write: bool,
    /// Refuse a committed census that is not the census of the workspace.
    #[arg(long)]
    check: bool,
    /// The root of the workspace.
    #[arg(long, default_value = ".")]
    root: PathBuf,
    /// Print each part of the run with its count and its time.
    #[arg(long)]
    cost: bool,
}

/// One part of a run: its name, its count of calls and its time.
///
/// # Specification
/// trivial.
struct Part
{
    /// The name of the part.
    name: &'static str,
    /// The time of the part.
    time: Duration,
}

/// Why a run gives no census.
///
/// # Specification
/// trivial.
enum Fault
{
    /// `cargo metadata` did not run, or it did not succeed.
    Cargo(String),
    /// A file could not be read or written.
    File(PathBuf, std::io::Error),
    /// The census refused the metadata or the committed text.
    Census(CensusError),
}

/// Run `cargo metadata` at `root` and read its census.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Fault::Cargo`] when `cargo metadata` does not run or does not succeed;
/// [`Fault::Census`] when its output does not read.
///
/// # Cost
/// - allocation: the output of `cargo metadata` and the census, setup
fn census(
    root: &Path,
    parts: &mut Vec<Part>,
) -> Result<Workspace, Fault>
{
    let started = Instant::now();
    let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
    let output = Command::new(cargo)
        .args([
            "metadata",
            "--format-version",
            "1",
            "--locked",
            "--manifest-path",
        ])
        .arg(root.join("Cargo.toml"))
        .output()
        .map_err(|error| Fault::Cargo(error.to_string()))?;
    parts.push(Part {
        name: "cargo metadata",
        time: started.elapsed(),
    });
    if !output.status.success() {
        return Err(Fault::Cargo(
            String::from_utf8_lossy(&output.stderr).trim().to_owned(),
        ));
    }
    let started = Instant::now();
    let workspace = Workspace::read(&output.stdout).map_err(Fault::Census)?;
    parts.push(Part {
        name: "read",
        time: started.elapsed(),
    });
    Ok(workspace)
}

/// Run the invocation `cli`, print what it wrote or found, and choose the
/// exit code.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The [`std::io::Error`] of the first write to a stream that failed.
///
/// # Cost
/// - allocation: the census, its text and the parts, setup
fn ran(
    cli: &Cli,
    stdout: &mut impl std::io::Write,
    stderr: &mut impl std::io::Write,
) -> std::io::Result<ExitCode>
{
    let mut parts = Vec::new();
    let path = cli.root.join(CENSUS_PATH);
    let outcome = census(&cli.root, &mut parts).and_then(|workspace| {
        let started = Instant::now();
        let text = workspace.render();
        parts.push(Part {
            name: "render",
            time: started.elapsed(),
        });
        let started = Instant::now();
        let result = if cli.write {
            std::fs::write(&path, &text).map_err(|error| Fault::File(path.clone(), error))
        }
        else {
            let committed =
                std::fs::read_to_string(&path).map_err(|error| Fault::File(path.clone(), error))?;
            stale(&committed, &text).map_err(Fault::Census)
        };
        parts.push(Part {
            name: if cli.write { "write" } else { "compare" },
            time: started.elapsed(),
        });
        result.map(|()| workspace.counts())
    });
    if cli.cost {
        for part in &parts {
            writeln!(
                stderr,
                "twin-census: {}: 1 call, {} µs",
                part.name,
                part.time.as_micros()
            )?;
        }
    }
    match outcome {
        Ok((under, all)) => {
            if cli.write {
                writeln!(stdout, "{}", path.display())?;
            }
            writeln!(stdout, "crates under the emitter: {under} of {all}")?;
            Ok(ExitCode::SUCCESS)
        },
        Err(Fault::Census(refusal @ CensusError::Stale { .. })) => {
            writeln!(stderr, "twin-census: {refusal}")?;
            Ok(ExitCode::from(STALE))
        },
        Err(Fault::Census(refusal)) => {
            writeln!(stderr, "twin-census: {refusal}")?;
            Ok(ExitCode::from(FAULTED))
        },
        Err(Fault::Cargo(reason)) => {
            writeln!(stderr, "twin-census: `cargo metadata` failed: {reason}")?;
            Ok(ExitCode::from(FAULTED))
        },
        Err(Fault::File(path, error)) => {
            writeln!(stderr, "twin-census: {}: {error}", path.display())?;
            Ok(ExitCode::from(FAULTED))
        },
    }
}

/// Parses the invocation, runs it and chooses the exit code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: exits as [`ran`] chooses; exits `2` when a stream cannot be
///   written, and after a usage message on standard error; exits `0` after
///   `--help` or `--version`.
/// - provides: the process boundary.
/// - fails: never; every fault is an exit code.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — the committed census checks against the workspace and
///   exits zero; a census with a changed row exits one and names its crate.
/// - witness: `tests::cli::the_committed_census_is_the_census_of_the_workspace`
/// - witness: `tests::cli::a_changed_row_exits_one_and_names_its_crate`
#[spec(ensures: |ret| ret == ExitCode::SUCCESS || ret == ExitCode::from(STALE) || ret == ExitCode::from(FAULTED))]
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
    ran(
        &cli,
        &mut std::io::stdout().lock(),
        &mut std::io::stderr().lock(),
    )
    .unwrap_or_else(|_unwritten| ExitCode::from(FAULTED))
}
