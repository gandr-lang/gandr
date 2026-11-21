//! `gate`: the bookkeeping of a landing's gate as one program.
//!
//! `gate inputs list <commit> <scope> <check>` prints the inputs of the check
//! over the scope at the commit, one per line: a path, a tab and its object.
//! `gate inputs digest --commit <commit>... --check <check>... <scope>`
//! prints one line for each commit and each check: the commit, the check and
//! the SHA-256 of that list, with tabs between them.
//!
//! `--tables <directory>` names the directory of `inputs.json` and
//! `verdicts.json`. `--times` prints each part of the run to standard error:
//! the sum of its times, the count of its calls and its name.
//! `GATE_INPUTS_TABLE` names another table than `inputs.json`, and
//! `GATE_INPUTS_TASK` gives the definition of each task, for the cases of a
//! scratch repository that holds no task.
//!
//! # Exit codes
//!
//! - `0`: the lines were printed; also `--help` and `--version`.
//! - `2`: a refusal — a failed call of git, of Cargo or of mise, a table that
//!   does not read, a check with no task, or standard output closed; also a
//!   malformed invocation.

use core::fmt::Write as _;
use std::io::Write as _;
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Instant;

use gandr_workflow_gate::Check;
use gandr_workflow_gate::Commit;
use gandr_workflow_gate::Elapsed;
use gandr_workflow_gate::Parts;
use gandr_workflow_gate::Request;
use gandr_workflow_gate::Scope;

/// The exit code of a refusal or a malformed invocation.
const REFUSED: u8 = 2;

/// The bookkeeping of a landing's gate.
#[derive(Debug, clap::Parser)]
#[command(name = "gate", version, about)]
struct Cli
{
    /// Print each part of the run to standard error: its time, its calls and
    /// its name.
    #[arg(long, global = true)]
    times: bool,
    /// The directory of `inputs.json` and `verdicts.json`. Without it, the
    /// run reads `.config/gate-scope` of the worktree.
    #[arg(long, global = true)]
    tables: Option<PathBuf>,
    /// What the run computes.
    #[command(subcommand)]
    command: Top,
}

/// The areas of the program.
#[derive(Debug, clap::Subcommand)]
enum Top
{
    /// The inputs of a check.
    #[command(subcommand)]
    Inputs(Inputs),
}

/// The commands on the inputs of a check.
#[derive(Debug, clap::Subcommand)]
enum Inputs
{
    /// Print the inputs of one check at one commit, one per line.
    List
    {
        /// The commit, or a tree.
        commit: Commit,
        /// The scope, as the package flags of Cargo.
        #[arg(allow_hyphen_values = true)]
        scope: Scope,
        /// The check's task name.
        check: Check,
    },
    /// Print the digest of the inputs of each check at each commit.
    Digest
    {
        /// A commit, or a tree; repeat for each.
        #[arg(long = "commit", required = true)]
        commits: Vec<Commit>,
        /// A check's task name; repeat for each.
        #[arg(long = "check", required = true)]
        checks: Vec<Check>,
        /// The scope, as the package flags of Cargo.
        #[arg(allow_hyphen_values = true)]
        scope: Scope,
    },
}

/// Runs the command, prints its lines and gives the exit code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `0` after the lines of the command are on standard output; `2`
///   after a refusal is on standard error as `gate:` and its message. With
///   `--times`, each part of the run is on standard error before the time of
///   the whole run.
/// - provides: the process boundary of the crate.
/// - fails: never; a refusal is an exit code.
/// - panics: none.
/// - executable: none — the outcome is the process's streams and status.
///
/// # Cost
/// - allocation: the request, the lists and the lines of the output, growth
///   within the pairs of the request
///
/// # Adequacy
/// - hypothesis: L2 — the lists and the digests of the script, and two
///   refusals; a digest in place of a list, or a refusal with status 0, changes
///   the asserted output or status.
/// - witness: `tests::cli::a_list_holds_each_input_of_its_scope`
/// - witness: `tests::cli::one_run_gives_each_pair_and_two_commits_with_one_tree_share_a_grep`
/// - witness: `tests::cli::a_check_that_mise_does_not_list_is_refused`
fn main() -> ExitCode
{
    let start = Instant::now();
    let cli = <Cli as clap::Parser>::parse();
    let (request, digests) = match cli.command {
        Top::Inputs(Inputs::List {
            commit,
            scope,
            check,
        }) => (
            Request {
                commits: vec![commit],
                checks: vec![check],
                scope,
                tables: cli.tables,
            },
            false,
        ),
        Top::Inputs(Inputs::Digest {
            commits,
            checks,
            scope,
        }) => (
            Request {
                commits,
                checks,
                scope,
                tables: cli.tables,
            },
            true,
        ),
    };
    let parts = Parts::default();
    let result = gandr_workflow_gate::lists(&request, &parts);
    let mut errors = std::io::stderr().lock();
    if cli.times {
        let _written = writeln!(
            errors,
            "{parts}gate: {}  the whole run",
            Elapsed::from(start.elapsed())
        );
    }
    match result {
        Ok(listed) => {
            let mut lines = String::new();
            for item in &listed {
                let _written = if digests {
                    writeln!(
                        lines,
                        "{}\t{}\t{}",
                        item.commit(),
                        item.check(),
                        item.list().digest()
                    )
                }
                else {
                    write!(lines, "{}", item.list())
                };
            }
            if std::io::stdout().write_all(lines.as_bytes()).is_err() {
                return ExitCode::from(REFUSED);
            }
            ExitCode::SUCCESS
        },
        Err(refusal) => {
            let _written = writeln!(errors, "gate: {refusal}");
            ExitCode::from(REFUSED)
        },
    }
}
