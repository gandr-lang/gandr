//! `gate`: the bookkeeping of a landing's gate as one program.
//!
//! # Boundaries
//!
//! The commands `inputs list`, `inputs digest`, `verdict key`, `verdict read`,
//! `verdict write`, `verdict publish`, `scope` and `scoped` are the rows of
//! the table of `README.md`, with what each prints.
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
//! |`GATE_HELD`|the checks that a gate held, which a write signs no record of|
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
//! - `1`: a read holds no record of a check, so the job runs it; or a write
//!   signs no record after two attempts.
//! - `2`: a refusal — a failed call of git, of Cargo, of mise, of GitHub or of
//!   the compiler, a table that does not read, a check with no task or with no
//!   row of a verdict, a read with no signing key, or standard output closed;
//!   also a malformed invocation, and a command of `scoped` that does not start
//!   or that a signal ends.
//! - The exit code of the command of `scoped` when it runs.

use core::fmt::Write as _;
use std::io::Write as _;
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Instant;

use gandr_workflow_gate::AdmitRequest;
use gandr_workflow_gate::Check;
use gandr_workflow_gate::Commit;
use gandr_workflow_gate::Elapsed;
use gandr_workflow_gate::End;
use gandr_workflow_gate::KeyRequest;
use gandr_workflow_gate::Part;
use gandr_workflow_gate::Parts;
use gandr_workflow_gate::Passing;
use gandr_workflow_gate::ReadRequest;
use gandr_workflow_gate::RecordRequest;
use gandr_workflow_gate::Request;
use gandr_workflow_gate::RequireRequest;
use gandr_workflow_gate::Scope;
use gandr_workflow_gate::ScopeRequest;
use gandr_workflow_gate::Scoped;
use gandr_workflow_gate::SendRequest;
use gandr_workflow_gate::WriteRequest;

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
    /// The records of the gates that passed on a tree.
    #[command(subcommand)]
    Pass(Pass),
    /// Print the scope of a change: `workspace`, `none`, or `packages` and
    /// the name of each crate that the change can break.
    Scope
    {
        /// The base of the change.
        #[arg(long)]
        base: Commit,
        /// The head of the change; the working tree without it.
        #[arg(long)]
        head: Option<Commit>,
        /// The touched crates alone, with no dependent.
        #[arg(long)]
        touched: bool,
    },
    /// Run a command one time for the scope of a change, with the package
    /// arguments of Cargo after it: `--workspace`, or `-p` and each name.
    Scoped
    {
        /// The base of the change.
        #[arg(long)]
        base: Commit,
        /// The head of the change; the working tree without it.
        #[arg(long)]
        head: Option<Commit>,
        /// The touched crates alone, with no dependent.
        #[arg(long)]
        touched: bool,
        /// The command, after `--`.
        #[arg(last = true, required = true)]
        command: Vec<String>,
    },
}

/// Writes the causes of a scope of the whole workspace to standard error.
///
/// # Specification
/// trivial.
fn causes(scoped: &Scoped)
{
    if let Scoped::Workspace(ref causes) = *scoped {
        let mut errors = std::io::stderr().lock();
        for cause in causes {
            let _written = writeln!(errors, "gate: the whole workspace: {cause}");
        }
    }
}

/// Runs `command` one time for the scope of `request`, with the package
/// arguments after it, and gives its exit code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: for no crate, nothing runs, `no package in scope` is on standard
///   output and the code is `0`. Else the scope is on standard error, the
///   command runs with the streams of this process, and the code is the
///   command's. A refusal of the scope, a command that does not start, and a
///   command that a signal ends give `2`.
/// - provides: one run of a gate command for the crates of a change.
/// - fails: never; a refusal is an exit code.
/// - panics: none.
/// - executable: none — the outcome is the process's streams and status.
fn scoped(
    request: &ScopeRequest,
    command: &[String],
    parts: &Parts,
) -> ExitCode
{
    let scope = match gandr_workflow_gate::scope(request, parts) {
        Ok(scope) => scope,
        Err(refusal) => {
            let _written = writeln!(std::io::stderr().lock(), "gate: {refusal}");
            return ExitCode::from(REFUSED);
        },
    };
    causes(&scope);
    if scope == Scoped::None {
        let _written = writeln!(std::io::stdout().lock(), "no package in scope");
        return ExitCode::SUCCESS;
    }
    let _written = writeln!(std::io::stderr().lock(), "gate: scope {scope}");
    let Some((program, arguments)) = command.split_first()
    else {
        return ExitCode::from(REFUSED);
    };
    let started = Instant::now();
    let status = std::process::Command::new(program)
        .args(arguments)
        .args(scope.arguments())
        .status();
    parts.add(Part::from("the scoped command"), started.elapsed());
    match status {
        Ok(status) => status
            .code()
            .and_then(|code| u8::try_from(code).ok())
            .map_or_else(|| ExitCode::from(REFUSED), ExitCode::from),
        Err(error) => {
            let _written = writeln!(
                std::io::stderr().lock(),
                "gate: {} does not start: {error}",
                command.join(" ")
            );
            ExitCode::from(REFUSED)
        },
    }
}

/// The commands on the records of passed gates.
#[derive(Debug, clap::Subcommand)]
enum Pass
{
    /// Print the tree of the work: the index, the working tree and each
    /// untracked path that git does not ignore.
    Tree,
    /// Record that a gate ran its checks on a tree and passed.
    Record
    {
        /// The name of the gate.
        gate: String,
        /// The tree that the gate passed on.
        tree: Commit,
        /// The log of the gate.
        log: PathBuf,
        /// The wall time of the gate in seconds.
        seconds: String,
        /// The wait of the gate, as `{"lane": <s>, "slot": <s>}`.
        wait: String,
        /// A check's task name that the gate ran; repeat for each.
        checks: Vec<Check>,
    },
    /// Exit 0 when a gate passed on the tree of a commit and ran the cheap set
    /// of `landing`.
    Require
    {
        /// The command that asks, which each line names.
        command: String,
        /// The head.
        commit: Commit,
    },
    /// Record here the pass of a gate on another host, from its records on
    /// standard input.
    Admit
    {
        /// The host whose gate passed.
        host: String,
        /// The head that the gate passed on.
        commit: Commit,
    },
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
    /// Sign one record of the checks that a gate ran on a tree, and name it by
    /// the ref of each check.
    Write
    {
        /// The tree that the gate passed on.
        tree: Commit,
        /// A check's task name that the gate ran; repeat for each.
        #[arg(required = true)]
        checks: Vec<Check>,
    },
    /// Push the records of the tree of a commit, in one push.
    Publish
    {
        /// The commit whose tree the records name.
        commit: Commit,
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
    // A verb of the records prints its facts to standard error, and its answer
    // to standard output.
    let printed = |passing: Passing| {
        let _written = std::io::stderr().lock().write_all(passing.lines.as_bytes());
        (passing.out, passing.end)
    };
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
        Top::Verdict(Verdict::Write { tree, checks }) => gandr_workflow_gate::write(
            &WriteRequest {
                tree,
                checks,
                held: given("GATE_HELD").map_or_else(Default::default, |held| {
                    held.split_whitespace().map(Check::from).collect()
                }),
                base: given("GATE_BASE").map(|base| Commit::from(base.as_str())),
                scope: Scope::from(given("GATE_SCOPE").as_deref().unwrap_or("--workspace")),
                tables: cli.tables,
            },
            &parts,
        )
        .map(|writing| {
            let _written = std::io::stderr().lock().write_all(writing.lines.as_bytes());
            (String::new(), writing.end)
        }),
        Top::Verdict(Verdict::Publish { commit }) => gandr_workflow_gate::send(
            &SendRequest {
                commit,
                remote: given("GATE_VERDICT_REMOTE").unwrap_or_else(|| "origin".to_owned()),
            },
            &parts,
        )
        .map(|sent| {
            let _written = std::io::stderr().lock().write_all(sent.lines.as_bytes());
            (String::new(), sent.end)
        }),
        Top::Pass(Pass::Tree) => {
            gandr_workflow_gate::tree(&parts).map(|tree| (format!("{tree}\n"), End::Held))
        },
        Top::Pass(Pass::Record {
            gate,
            tree,
            log,
            seconds,
            wait,
            checks,
        }) => gandr_workflow_gate::record(
            &RecordRequest {
                gate,
                tree,
                log,
                seconds,
                wait,
                checks,
            },
            &parts,
        )
        .map(printed),
        Top::Pass(Pass::Require { command, commit }) => {
            gandr_workflow_gate::require(&RequireRequest { command, commit }, &parts).map(printed)
        },
        Top::Pass(Pass::Admit { host, commit }) => gandr_workflow_gate::admit(
            &AdmitRequest {
                host,
                commit,
                // Input that does not read is a stream of no record.
                records: std::io::read_to_string(std::io::stdin()).unwrap_or_default(),
            },
            &parts,
        )
        .map(printed),
        Top::Scope {
            base,
            head,
            touched,
        } => gandr_workflow_gate::scope(
            &ScopeRequest {
                base,
                head,
                touched,
            },
            &parts,
        )
        .map(|scope| {
            causes(&scope);
            (format!("{scope}\n"), End::Held)
        }),
        Top::Scoped {
            base,
            head,
            touched,
            command,
        } => {
            let code = scoped(
                &ScopeRequest {
                    base,
                    head,
                    touched,
                },
                &command,
                &parts,
            );
            if cli.times {
                let _written = writeln!(
                    std::io::stderr().lock(),
                    "{parts}gate: {}  the whole run",
                    Elapsed::from(start.elapsed())
                );
            }
            return code;
        },
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
