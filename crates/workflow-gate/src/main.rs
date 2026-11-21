//! `gate`: the bookkeeping of a landing's gate as one program.
//!
//! # Boundaries
//!
//! `gate inputs list <commit> <scope> <check>` prints the inputs of the check
//! over the scope at the commit, one per line: a path, a tab and its object.
//! `gate inputs digest --commit <commit>... --check <check>... <scope>`
//! prints one line for each commit and each check: the commit, the check and
//! the SHA-256 of that list, with tabs between them.
//!
//! `gate verdict key [--tree <tree>] <check>...` prints the key of the
//! verdict of each check, one line of JSON each. `gate verdict read
//! <check>...` reads which check holds on the tree of `HEAD`, by the inputs of
//! its base or by a signed record of a pass on the remote. It prints one line
//! for each fact to standard error.
//!
//! `--tables <directory>` names the directory of `inputs.json`,
//! `verdicts.json` and the scope script. `--times` prints each part of the
//! run to standard error: the sum of its times, the count of its calls and
//! its name.
//!
//! The variables of the environment that the commands read are these.
//!
//! |Variable|What it gives|
//! |---|---|
//! |`GATE_BASE`|the base of the change|
//! |`GATE_SCOPE`|the scope of each check of a key|
//! |`GATE_VERDICT_RUSTC`|another compiler than `rustc`|
//! |`GATE_VERDICT_POLICY`|the revision of the policy|
//! |`GATE_VERDICT_REMOTE`|the remote of the records, `origin` by default|
//! |`GATE_VERDICT_SCOPE`|the scope of a read|
//! |`GATE_VERDICT_SIGNERS`|a file of allowed signers|
//! |`GATE_VERDICT_TRUNK_OK`|the bases that the trunk holds|
//! |`GATE_INPUTS_TABLE`|another table than `inputs.json`|
//! |`GATE_INPUTS_TASK`|the definition of each task, for a scratch repository that holds no task|
//!
//! The exit codes are these.
//!
//! - `0`: the lines were printed, or each check of a read holds; also `--help`
//!   and `--version`.
//! - `1`: a read holds no record of a check, so the job runs it.
//! - `2`: a refusal — a failed call of git, of Cargo, of mise, of GitHub or of
//!   the compiler, a table that does not read, a check with no task or with no
//!   row of a verdict, a read with no signing key, or standard output closed;
//!   also a malformed invocation.

use core::fmt::Write as _;
use std::io::Write as _;
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Instant;

use gandr_workflow_gate::Check;
use gandr_workflow_gate::Commit;
use gandr_workflow_gate::Elapsed;
use gandr_workflow_gate::End;
use gandr_workflow_gate::KeyRequest;
use gandr_workflow_gate::Parts;
use gandr_workflow_gate::ReadRequest;
use gandr_workflow_gate::Request;
use gandr_workflow_gate::Scope;

/// The exit code of a read that holds no record of a check.
const RUNS: u8 = 1;

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
    /// The verdict of a check.
    #[command(subcommand)]
    Verdict(Verdict),
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

/// The commands on the verdict of a check.
#[derive(Debug, clap::Subcommand)]
enum Verdict
{
    /// Print the key of the verdict of each check, one line each.
    Key
    {
        /// The tree of the verdict; the tree of `HEAD` without it.
        #[arg(long)]
        tree: Option<Commit>,
        /// A check's task name; repeat for each.
        #[arg(required = true)]
        checks: Vec<Check>,
    },
    /// Read which check holds on the tree of `HEAD`, by its base or by a
    /// record, one line for each fact.
    Read
    {
        /// A check's task name; repeat for each.
        #[arg(required = true)]
        checks: Vec<Check>,
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
    let parts = Parts::default();
    // A variable that is set and not empty: an empty `GATE_BASE` binds the
    // empty base, as the script read it.
    let given = |name: &str| std::env::var(name).ok().filter(|value| !value.is_empty());
    let result = match cli.command {
        Top::Inputs(Inputs::List {
            commit,
            scope,
            check,
        }) => gandr_workflow_gate::lists(
            &Request {
                commits: vec![commit],
                checks: vec![check],
                scope,
                tables: cli.tables,
            },
            &parts,
        )
        .map(|listed| {
            let mut lines = String::new();
            for item in &listed {
                let _written = write!(lines, "{}", item.list());
            }
            (lines, End::Held)
        }),
        Top::Inputs(Inputs::Digest {
            commits,
            checks,
            scope,
        }) => gandr_workflow_gate::lists(
            &Request {
                commits,
                checks,
                scope,
                tables: cli.tables,
            },
            &parts,
        )
        .map(|listed| {
            let mut lines = String::new();
            for item in &listed {
                let _written = writeln!(
                    lines,
                    "{}\t{}\t{}",
                    item.commit(),
                    item.check(),
                    item.list().digest()
                );
            }
            (lines, End::Held)
        }),
        Top::Verdict(Verdict::Key { tree, checks }) => gandr_workflow_gate::keys(
            &KeyRequest {
                checks,
                tree,
                base: given("GATE_BASE").map(|base| Commit::from(base.as_str())),
                scope: Scope::from(given("GATE_SCOPE").as_deref().unwrap_or("--workspace")),
                tables: cli.tables,
            },
            &parts,
        )
        .map(|keys| {
            let mut lines = String::new();
            for key in &keys {
                let _written = writeln!(lines, "{key}");
            }
            (lines, End::Held)
        }),
        Top::Verdict(Verdict::Read { checks }) => gandr_workflow_gate::read(
            &ReadRequest {
                checks,
                tables: cli.tables,
                base: given("GATE_BASE").map(|base| Commit::from(base.as_str())),
                scope: given("GATE_VERDICT_SCOPE").map(|scope| Scope::from(scope.as_str())),
                signers: given("GATE_VERDICT_SIGNERS").map(PathBuf::from),
                trunk_holds: std::env::var("GATE_VERDICT_TRUNK_OK").ok(),
                remote: given("GATE_VERDICT_REMOTE").unwrap_or_else(|| "origin".to_owned()),
                trunk: given("GANDR_TRUNK").unwrap_or_else(|| "landing".to_owned()),
                token: given("GITHUB_ACTIONS").and_then(|_hosted| given("GH_TOKEN")),
            },
            &parts,
        )
        .map(|reading| {
            let _written = std::io::stderr().lock().write_all(reading.lines.as_bytes());
            (String::new(), reading.end)
        }),
    };
    let mut errors = std::io::stderr().lock();
    if cli.times {
        let _written = writeln!(
            errors,
            "{parts}gate: {}  the whole run",
            Elapsed::from(start.elapsed())
        );
    }
    match result {
        Ok((lines, end)) => {
            if std::io::stdout().write_all(lines.as_bytes()).is_err() {
                return ExitCode::from(REFUSED);
            }
            match end {
                End::Held => ExitCode::SUCCESS,
                End::Runs => ExitCode::from(RUNS),
                End::Refused => ExitCode::from(REFUSED),
            }
        },
        Err(refusal) => {
            let _written = writeln!(errors, "gate: {refusal}");
            ExitCode::from(REFUSED)
        },
    }
}
