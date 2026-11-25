//! `twin-census`: writes or checks `ledger/twin-census.md`, the census of the
//! crates under the emitter and of their generic public items.
//!
//! | Invocation | Does | Exits `1` when |
//! | --- | --- | --- |
//! | `twin-census --write [--root <directory>]` | writes the census and prints its path and its counts | never |
//! | `twin-census --check [--root <directory>]` | compares the committed census with the census of the workspace | the census is stale |
//!
//! A run starts `cargo metadata` one time and `cargo doc` one time, for the
//! library of each crate of the workspace. `cargo doc` writes rustdoc's JSON
//! to `twin-census/doc/` below the target directory of the workspace, with
//! each lint of rustdoc capped at a warning: the census reads the items, not
//! the documentation. The run reads the files at the same time, one thread
//! for each core.
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
//! - `2`: `cargo metadata` or `cargo doc` that does not run or does not
//!   succeed, metadata or JSON of rustdoc that does not read, a file that
//!   cannot be read or written, output that cannot be written, or a malformed
//!   invocation.

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
use gandr_workflow_twin_census::rustdoc;
use gandr_workflow_twin_census::rustdoc::Surface;
use gandr_workflow_twin_census::stale;
use rayon::iter::IntoParallelRefIterator as _;
use rayon::iter::ParallelIterator as _;

/// The exit code of a stale census.
const STALE: u8 = 1;

/// The exit code of a fault or a malformed invocation.
const FAULTED: u8 = 2;

/// The flags of rustdoc: its JSON, with each lint a warning.
const RUSTDOCFLAGS: &str = "-Z unstable-options --output-format json --cap-lints warn";

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
    /// The count of calls of the part.
    calls: usize,
    /// The time of the part.
    time: Duration,
}

/// Why a run gives no census.
///
/// # Specification
/// trivial.
enum Fault
{
    /// A command of Cargo did not run, or it did not succeed.
    Cargo(&'static str, String),
    /// A file could not be read or written.
    File(PathBuf, std::io::Error),
    /// The census refused the metadata or the committed text.
    Census(CensusError),
    /// The census refused the JSON of rustdoc in a file.
    Rustdoc(PathBuf, CensusError),
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
        .map_err(|error| Fault::Cargo("metadata", error.to_string()))?;
    parts.push(Part {
        name: "cargo metadata",
        calls: 1,
        time: started.elapsed(),
    });
    if !output.status.success() {
        return Err(Fault::Cargo(
            "metadata",
            String::from_utf8_lossy(&output.stderr).trim().to_owned(),
        ));
    }
    let started = Instant::now();
    let workspace = Workspace::read(&output.stdout).map_err(Fault::Census)?;
    parts.push(Part {
        name: "read",
        calls: 1,
        time: started.elapsed(),
    });
    Ok(workspace)
}

/// Run `cargo doc` at `root` for the library of each crate of `workspace`,
/// read the JSON of each library, and put its counts in the row of its crate.
///
/// # Specification
/// trivial.
///
/// # Errors
/// [`Fault::Cargo`] when `cargo doc` does not run or does not succeed;
/// [`Fault::File`] when a file of rustdoc cannot be read;
/// [`Fault::Rustdoc`] when it does not read as rustdoc's JSON.
///
/// # Cost
/// - allocation: the output of `cargo doc`, and the bytes and the index of each
///   file at the same time on each thread, setup
fn surfaces(
    root: &Path,
    workspace: &mut Workspace,
    parts: &mut Vec<Part>,
) -> Result<(), Fault>
{
    let started = Instant::now();
    let target = Path::new(workspace.target_directory()).join("twin-census");
    let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
    let output = Command::new(cargo)
        .args([
            "doc",
            "--workspace",
            "--no-deps",
            "--lib",
            "--locked",
            "--quiet",
            "--manifest-path",
        ])
        .arg(root.join("Cargo.toml"))
        .env("RUSTDOCFLAGS", RUSTDOCFLAGS)
        .env("CARGO_TARGET_DIR", &target)
        .output()
        .map_err(|error| Fault::Cargo("doc", error.to_string()))?;
    parts.push(Part {
        name: "cargo doc",
        calls: 1,
        time: started.elapsed(),
    });
    if !output.status.success() {
        return Err(Fault::Cargo(
            "doc",
            String::from_utf8_lossy(&output.stderr).trim().to_owned(),
        ));
    }
    let started = Instant::now();
    let doc = target.join("doc");
    let libraries: Vec<(String, PathBuf)> = workspace
        .libraries()
        .map(|(name, library)| (name.to_owned(), doc.join(format!("{library}.json"))))
        .collect();
    let surfaces: Vec<Result<Surface, Fault>> = libraries
        .par_iter()
        .map(|&(_, ref path)| {
            let bytes = std::fs::read(path).map_err(|error| Fault::File(path.clone(), error))?;
            rustdoc::read(&bytes).map_err(|refusal| Fault::Rustdoc(path.clone(), refusal))
        })
        .collect();
    parts.push(Part {
        name: "read rustdoc",
        calls: libraries.len(),
        time: started.elapsed(),
    });
    for (&(ref name, _), surface) in libraries.iter().zip(surfaces) {
        workspace.set_surface(name, surface?);
    }
    Ok(())
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
    let outcome = census(&cli.root, &mut parts).and_then(|mut workspace| {
        surfaces(&cli.root, &mut workspace, &mut parts)?;
        let started = Instant::now();
        let text = workspace.render();
        parts.push(Part {
            name: "render",
            calls: 1,
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
            calls: 1,
            time: started.elapsed(),
        });
        result.map(|()| workspace.counts())
    });
    if cli.cost {
        for part in &parts {
            writeln!(
                stderr,
                "twin-census: {}: {} {}, {} µs",
                part.name,
                part.calls,
                if part.calls == 1 { "call" } else { "calls" },
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
        Err(Fault::Cargo(command, reason)) => {
            writeln!(stderr, "twin-census: `cargo {command}` failed: {reason}")?;
            Ok(ExitCode::from(FAULTED))
        },
        Err(Fault::Rustdoc(path, refusal)) => {
            writeln!(stderr, "twin-census: {}: {refusal}", path.display())?;
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
