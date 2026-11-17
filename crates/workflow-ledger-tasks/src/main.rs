//! `ledger`: the ledger tasks of gandr's surface, one verb each.
//!
//! | Invocation | Prints | Exits `1` when |
//! | --- | --- | --- |
//! | `ledger syntax --write <directory> [--exemplars <directory>]` | the path of each file written, `syntax.md` then `syntax.json`, each committed rule's admission read off its exemplar | never |
//! | `ledger exemplars <directory>` | each exemplar that does not hold, `<path>: <fault>`, then the count verified and found | an exemplar does not hold |
//! | `ledger recovery <directory>` | the near-miss table, each mutant whose first error marks other bytes than its mutation, then the count swept | a mutant is marked elsewhere |
//! | `ledger list [--area <area>] [--status <status>] [--root <directory>]` | one line for each feature, `<id> [<status>] <name>: <line>` | never |
//! | `ledger show <id> [--root <directory>]` | the feature's row, each of its exemplars' sources whole, then its corpus paths | never |
//!
//! The binary exits with one of three codes:
//!
//! - `0`: the ledger was written, every exemplar held, the sweep marked every
//!   mutant at its mutation, or the features were read; also `--help` and
//!   `--version`.
//! - `1`: an exemplar does not hold, or a mutant's first error marks other
//!   bytes than its mutation.
//! - `2`: a ledger that cannot be generated, written, listed, read or answer,
//!   output that cannot be written, or a malformed invocation.

use std::io::Write;
use std::path::PathBuf;
use std::process::ExitCode;

use anodized::spec;
use gandr_surface_features::Area;
use gandr_surface_features::FeatureId;
use gandr_surface_features::Status;
use gandr_workflow_ledger_tasks::LedgerRun;
use gandr_workflow_ledger_tasks::LedgerTask;

/// The exit code of an exemplar that does not hold, or of a mutant marked
/// elsewhere.
const FOUND: u8 = 1;

/// The exit code of a fault or a malformed invocation.
const FAULTED: u8 = 2;

/// The ledger tasks of gandr's surface.
#[derive(Debug, clap::Parser)]
#[command(name = "ledger", version, about)]
enum Cli
{
    /// The syntax ledger: every rule of the built-in grammar and every
    /// attribute of the lowering's registry, under the grammar's fingerprint,
    /// as `syntax.md` for reading and `syntax.json` for machines.
    Syntax
    {
        /// The directory both files are written into, created when missing.
        #[arg(long, value_name = "DIRECTORY")]
        write: PathBuf,
        /// The directory holding `syntax/`, whose exemplars each committed
        /// rule's admission is read off; `exemplars/` under the written
        /// directory when not given.
        #[arg(long, value_name = "DIRECTORY")]
        exemplars: Option<PathBuf>,
    },
    /// The syntax exemplars: one source per committed rule under `syntax/`
    /// and per attribute under `attributes/`, each parsed and checked for the
    /// form it names.
    Exemplars
    {
        /// The directory holding `syntax/` and `attributes/`.
        directory: PathBuf,
    },
    /// The recovery sweep: every literal tile of every syntax exemplar under
    /// `syntax/` written as its near miss and deleted, and each mutant's first
    /// error read against the bytes it changed.
    Recovery
    {
        /// The directory holding `syntax/`.
        directory: PathBuf,
    },
    /// The features ledger, one line per feature: its id, status, name and
    /// what it is. Before writing a form, list its area.
    List
    {
        /// Only the features in this area, such as `syntax`.
        #[arg(long)]
        area: Option<String>,
        /// Only the features at this status.
        #[arg(long, value_enum)]
        status: Option<StatusName>,
        /// The tree holding `ledger/features.sql`.
        #[arg(long, value_name = "DIRECTORY", default_value = ".")]
        root: PathBuf,
    },
    /// One feature of the features ledger: its row, each of its exemplars'
    /// sources whole and its corpus witnesses' paths. Show each feature a form
    /// uses before writing it.
    Show
    {
        /// The feature's id, as `ledger list` prints it.
        id: String,
        /// The tree holding `ledger/features.sql` and the paths it names.
        #[arg(long, value_name = "DIRECTORY", default_value = ".")]
        root: PathBuf,
    },
}

/// A status `list --status` names.
#[derive(Clone, Copy, Debug, Eq, PartialEq, clap::ValueEnum)]
enum StatusName
{
    /// gandr has it.
    Implemented,
    /// gandr has part of it.
    Partial,
    /// gandr will have it.
    Planned,
    /// gandr will not have it.
    Declined,
}

impl From<StatusName> for Status
{
    /// The status `name` names.
    ///
    /// # Specification
    /// trivial.
    ///
    /// # Adequacy
    /// - hypothesis: L3 — `--status planned` lists only the planned feature, so
    ///   a name read as another status lists another set.
    /// - witness: `tests::cli::the_features_ledger_lists_and_shows_1827`
    #[inline]
    fn from(name: StatusName) -> Self
    {
        match name {
            StatusName::Implemented => Self::Implemented,
            StatusName::Partial => Self::Partial,
            StatusName::Planned => Self::Planned,
            StatusName::Declined => Self::Declined,
        }
    }
}

/// The task an invocation names.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each verb maps to the [`LedgerTask`] of the same name, with its
///   paths, its area, its status and its id unchanged; `syntax` reads its
///   exemplars under `exemplars/` of the written directory when the invocation
///   names none.
/// - provides: the verbs' vocabulary over the tasks.
/// - fails: never.
/// - panics: none.
/// - executable: none — the map is one match over the verbs, and a predicate
///   would restate that match.
///
/// # Adequacy
/// - hypothesis: L3 — as [`main`].
/// - witness: `tests::cli::the_syntax_ledger_is_written_and_reproduced`
/// - witness: `tests::cli::the_features_ledger_lists_and_shows_1827`
fn task(cli: Cli) -> LedgerTask
{
    match cli {
        Cli::Syntax { write, exemplars } => LedgerTask::Syntax {
            exemplars: exemplars.unwrap_or_else(|| write.join("exemplars")),
            directory: write,
        },
        Cli::Exemplars { directory } => LedgerTask::Exemplars { directory },
        Cli::Recovery { directory } => LedgerTask::Recovery { directory },
        Cli::List { area, status, root } => LedgerTask::List {
            root,
            area: area.map(Area),
            status: status.map(Status::from),
        },
        Cli::Show { id, root } => LedgerTask::Show {
            root,
            id: FeatureId(id),
        },
    }
}

/// Parses the invocation, runs its task and chooses the exit code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: exits as [`ran`] chooses; exits `2` when standard output or
///   standard error cannot be written, and after printing a usage message to
///   standard error; exits `0` after `--help` or `--version`.
/// - provides: the process boundary.
/// - fails: never; every fault is an exit code.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a written ledger, a stray exemplar, a sweep, a list, a
///   show and an unknown area exit `0`, `1` and `2` as their cases state; a
///   swapped stream or exit code changes the observed process result.
/// - witness: `tests::cli::the_syntax_ledger_is_written_and_reproduced`
/// - witness: `tests::cli::the_exemplars_verify_and_a_stray_one_is_named`
/// - witness: `tests::cli::the_recovery_sweep_reports_its_table_and_count`
/// - witness: `tests::cli::the_features_ledger_lists_and_shows_1827`
#[spec(ensures: |ret| ret == ExitCode::SUCCESS || ret == ExitCode::from(FOUND) || ret == ExitCode::from(FAULTED))]
fn main() -> ExitCode
{
    let cli = match <Cli as clap::Parser>::try_parse() {
        Ok(cli) => cli,
        Err(error) => {
            return match (error.print(), error.use_stderr()) {
                (Ok(()), false) => ExitCode::SUCCESS,
                (Ok(()), true) | (Err(_), _) => ExitCode::from(FAULTED),
            };
        },
    };
    let task = task(cli);
    ran(
        &task,
        &mut std::io::stdout().lock(),
        &mut std::io::stderr().lock(),
    )
    .unwrap_or_else(|_| ExitCode::from(FAULTED))
}

/// Run `task`, printing what it wrote, verified, swept or read, and choose
/// the exit code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a written ledger prints each file's path on standard output and
///   exits zero. A verification prints each exemplar that does not hold as
///   `<path>: <fault>`, then the count verified and found, on standard output;
///   a recovery sweep prints its near-miss table, each mutant marked elsewhere,
///   then the count swept. Each exits zero when nothing was found and one
///   otherwise. A list prints each feature it matched as `<id> [<status>]
///   <name>: <line>`, a show prints the feature's row, its exemplars' sources
///   and its corpus paths, and both exit zero. A ledger that cannot be
///   generated, written, listed, read or answer is `ledger: <fault>` on
///   standard error and exits two.
/// - provides: `ledger syntax --write <directory>`, `ledger exemplars
///   <directory>`, `ledger recovery <directory>`, `ledger list` and `ledger
///   show <id>`.
/// - fails: the first write error on either stream.
/// - panics: none.
///
/// # Errors
/// The [`std::io::Error`] of the first write that failed.
///
/// # Adequacy
/// - hypothesis: L3 — a run into a fresh directory prints both paths, exits
///   zero and leaves files that a second run reproduces byte for byte; a
///   directory under a file exits two naming it; the committed exemplars verify
///   and exit zero, and a stray exemplar exits one naming it; a sweep prints
///   its near-miss table and its count; a list and a show of a scratch ledger
///   print their golden and exit zero, and an unknown area and id exit two
///   naming them.
/// - witness: `tests::cli::the_syntax_ledger_is_written_and_reproduced`
/// - witness: `tests::cli::the_exemplars_verify_and_a_stray_one_is_named`
/// - witness: `tests::cli::the_recovery_sweep_reports_its_table_and_count`
/// - witness: `tests::cli::the_features_ledger_lists_and_shows_1827`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |exit|
    *exit == ExitCode::SUCCESS || *exit == ExitCode::from(FOUND) || *exit == ExitCode::from(FAULTED)))]
fn ran(
    task: &LedgerTask,
    stdout: &mut impl Write,
    stderr: &mut impl Write,
) -> std::io::Result<ExitCode>
{
    match task.run() {
        Ok(LedgerRun::Written(paths)) => {
            for path in paths {
                writeln!(stdout, "{}", path.display())?;
            }
            Ok(ExitCode::SUCCESS)
        },
        Ok(LedgerRun::Verified(report)) => {
            for finding in report.findings() {
                writeln!(stdout, "{finding}")?;
            }
            writeln!(stdout, "{report}")?;
            Ok(if report.findings().is_empty() {
                ExitCode::SUCCESS
            }
            else {
                ExitCode::from(FOUND)
            })
        },
        Ok(LedgerRun::Swept(report)) => {
            writeln!(stdout, "{report}")?;
            Ok(if report.findings().is_empty() {
                ExitCode::SUCCESS
            }
            else {
                ExitCode::from(FOUND)
            })
        },
        Ok(LedgerRun::Listed(features)) => {
            for feature in features {
                writeln!(stdout, "{feature}")?;
            }
            Ok(ExitCode::SUCCESS)
        },
        Ok(LedgerRun::Shown(shown)) => {
            write!(stdout, "{shown}")?;
            Ok(ExitCode::SUCCESS)
        },
        Err(fault) => {
            writeln!(stderr, "ledger: {fault}")?;
            Ok(ExitCode::from(FAULTED))
        },
    }
}
