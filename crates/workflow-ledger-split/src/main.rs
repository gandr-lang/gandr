//! `ledger-split`: writes the `sqlite3` dump of a ledger to the files of the
//! tree.
//!
//! | Invocation | Does | Exits `1` when |
//! | --- | --- | --- |
//! | `ledger-split --schema <file> --rows <path> <dump>` | writes the schema to `<file>` and the rows of each name to `<path>` with `{}` as the name | never |
//!
//! With `--cost`, the binary prints each part of the run on standard error,
//! with its count and its time.
//!
//! The binary exits with one of two codes:
//!
//! - `0`: the dump is split; also `--help` and `--version`.
//! - `2`: a dump that cannot be read, a row with no plain name, a file that
//!   cannot be written, a path of the rows with not one `{}`, output that
//!   cannot be written, or a malformed invocation.

use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Instant;

use anodized::spec;
use gandr_workflow_ledger_split::RowPath;
use gandr_workflow_ledger_split::split;

/// The exit code of a fault or a malformed invocation.
const FAULTED: u8 = 2;

/// Writes the `sqlite3` dump of a ledger to the files of the tree: the schema,
/// and the rows of each name, the first value of a row, in a file of their
/// own. The directory of each file exists before the split.
#[derive(Debug, clap::Parser)]
#[command(name = "ledger-split", version, about)]
struct Cli
{
    /// The file that the lines of the schema go to.
    #[arg(long, value_name = "FILE")]
    schema: PathBuf,
    /// The file of the rows of a name, with `{}` in the place of the name,
    /// such as `crates/{}/purposes.sql`.
    #[arg(long, value_name = "PATH")]
    rows: String,
    /// Print each part of the run with its count and its time.
    #[arg(long)]
    cost: bool,
    /// The dump, as `sqlite3 <database> .dump` writes it.
    dump: PathBuf,
}

/// Run the invocation `cli`, print each file that it wrote, and choose the
/// exit code.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The [`std::io::Error`] of the first write to a stream that failed.
///
/// # Cost
/// - allocation: the text of the dump and of each file, setup
fn ran(
    cli: &Cli,
    stdout: &mut impl std::io::Write,
    stderr: &mut impl std::io::Write,
) -> std::io::Result<ExitCode>
{
    let rows = match RowPath::new(&cli.rows) {
        Ok(rows) => rows,
        Err(fault) => {
            writeln!(stderr, "ledger-split: {fault}")?;
            return Ok(ExitCode::from(FAULTED));
        },
    };
    let start = Instant::now();
    let text = match std::fs::read_to_string(&cli.dump) {
        Ok(text) => text,
        Err(error) => {
            writeln!(
                stderr,
                "ledger-split: {}: cannot read: {error}",
                cli.dump.display()
            )?;
            return Ok(ExitCode::from(FAULTED));
        },
    };
    let read = start.elapsed();
    let start = Instant::now();
    let split = match split(&text, &cli.schema, &rows) {
        Ok(split) => split,
        Err(fault) => {
            writeln!(stderr, "ledger-split: {fault}")?;
            return Ok(ExitCode::from(FAULTED));
        },
    };
    let written = start.elapsed();
    for path in &split.paths {
        writeln!(stdout, "{}", path.display())?;
    }
    if cli.cost {
        writeln!(
            stderr,
            "ledger-split: read: 1 call, {} µs",
            read.as_micros()
        )?;
        writeln!(
            stderr,
            "ledger-split: split and write: {} lines, {} files, {} µs",
            split.lines,
            split.paths.len(),
            written.as_micros()
        )?;
    }
    Ok(ExitCode::SUCCESS)
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
/// - hypothesis: L3 — a dump splits, prints each file and its cost, and exits
///   zero; a dump with a row of no plain name exits two and names its line.
/// - witness: `tests::cli::a_dump_splits_and_prints_each_file`
/// - witness: `tests::cli::a_row_of_no_plain_name_exits_two_and_names_its_line`
#[spec(ensures: |ret| ret == ExitCode::SUCCESS || ret == ExitCode::from(FAULTED))]
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
