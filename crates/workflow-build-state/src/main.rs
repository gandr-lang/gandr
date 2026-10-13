//! `build-state`: prunes a Cargo profile directory to the units the
//! recorded builds used.
//!
//! `build-state prune --profile-dir DIR MESSAGES...` reads each file of
//! Cargo JSON messages, removes every unit's entries in `DIR` that none of
//! them names, and prints what it removed and kept.
//!
//! # Exit codes
//!
//! - `0`: the directory was pruned; also `--help` and `--version`.
//! - `2`: a refusal — a message file could not be read, is not Cargo's JSON,
//!   records an incomplete or failed build, or the directory could not be read
//!   or pruned; also a malformed invocation.

use std::io::Write as _;
use std::path::PathBuf;
use std::process::ExitCode;

use anodized::spec;
use gandr_workflow_build_state::BuildStateError;
use gandr_workflow_build_state::Messages;
use gandr_workflow_build_state::Units;
use gandr_workflow_build_state::prune;

/// The exit code of a refusal or a malformed invocation.
const REFUSED: u8 = 2;

/// Bytes in a mebibyte, the unit the report prints.
const MEBIBYTE: u64 = 0x0010_0000;

/// Keeps a Cargo build directory the size of the builds that use it.
#[repr(transparent)]
#[derive(Debug, clap::Parser)]
#[command(name = "build-state", version, about)]
struct Cli
{
    /// What to do.
    #[command(subcommand)]
    command: Command,
}

/// The subcommands.
#[derive(Debug, clap::Subcommand)]
enum Command
{
    /// Removes every unit's files that no recorded build used.
    Prune
    {
        /// The profile directory: `target/debug`, or the `debug` directory of
        /// another target directory.
        #[arg(long)]
        profile_dir: PathBuf,
        /// Files of Cargo JSON messages, one per build whose units are kept.
        #[arg(required = true)]
        messages: Vec<PathBuf>,
    },
}

/// Parses the invocation, prunes and chooses the exit code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: exits `0` after printing the prune's report, help or version;
///   exits `2` after printing a refusal or a usage message to standard error.
/// - provides: the process boundary.
/// - fails: never; every refusal is an exit code.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a prune, a failed build's messages, a missing file and an
///   invocation without message files; a swapped stream or exit code changes
///   the observed process result.
/// - witness: `cli::cli::a_prune_reports_what_it_removed`
/// - witness: `cli::cli::a_refusal_removes_nothing_and_exits_two`
/// - witness: `cli::cli::a_malformed_invocation_exits_two`
#[spec(ensures: |ret| ret == ExitCode::SUCCESS || ret == ExitCode::from(REFUSED))]
fn main() -> ExitCode
{
    let cli = match <Cli as clap::Parser>::try_parse() {
        | Ok(cli) => cli,
        | Err(error) => {
            return match (error.print(), error.use_stderr()) {
                | (Ok(()), false) => ExitCode::SUCCESS,
                | (Ok(()), true) | (Err(_), _) => ExitCode::from(REFUSED),
            };
        },
    };
    match run(cli) {
        | Ok(()) => ExitCode::SUCCESS,
        | Err(error) => match writeln!(std::io::stderr(), "build-state: {error}") {
            | Ok(()) | Err(_) => ExitCode::from(REFUSED),
        },
    }
}

/// Runs the subcommand `cli` names.
///
/// # Specification
/// - requires: nothing.
/// - ensures: every message file is read before anything is removed; on success
///   the directory is pruned and standard output receives one line naming the
///   entries and mebibytes removed and the entries kept.
/// - provides: the whole subcommand.
/// - fails: [`BuildStateError::Io`] when a message file cannot be read; every
///   refusal of [`Units::read`] and [`prune()`]; [`BuildStateError::Output`]
///   when standard output cannot be written.
/// - panics: none.
/// - executable: none — the outcome is the directory on disk and the bytes on
///   standard output.
///
/// # Errors
/// As `fails` lists.
///
/// # Adequacy
/// - hypothesis: L3 — a prune of a profile with one superseded library reports
///   it; a failed build's messages remove nothing.
/// - witness: `cli::cli::a_prune_reports_what_it_removed`
/// - witness: `cli::cli::a_refusal_removes_nothing_and_exits_two`
fn run(cli: Cli) -> Result<(), BuildStateError>
{
    let Command::Prune {
        profile_dir,
        messages,
    } = cli.command;
    let mut units = Units::default();
    for path in &messages {
        let text = std::fs::read_to_string(path).map_err(|error| BuildStateError::Io {
            path: path.clone(),
            message: error.to_string(),
        })?;
        units.read(path, Messages::from(text.as_str()))?;
    }
    let pruned = prune(&profile_dir, &units)?;
    writeln!(
        std::io::stdout(),
        "pruned {} entries, {} MiB, from {}; kept {}",
        pruned.removed,
        pruned.bytes.checked_div(MEBIBYTE).unwrap_or_default(),
        profile_dir.display(),
        pruned.kept
    )
    .map_err(|error| BuildStateError::Output {
        message: error.to_string(),
    })
}
