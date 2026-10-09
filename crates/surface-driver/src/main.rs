//! Driver binary for the gandr language toolchain.
//!
//! Installs as `gandr`. The driver owns the argument surface and the process
//! boundary: it parses an invocation, routes it through the surface
//! dispatcher, renders the outcome, and reports the run through its exit
//! code.
//!
//! # Exit codes
//!
//! - `0`: every declaration settled; also `--help`, `--version` and a bare
//!   invocation.
//! - `1`: at least one declaration is unsettled, or a source was not read as
//!   its root expects.
//! - `2`: an engine fault, an unreadable source or a path naming none, a
//!   malformed invocation, or output the driver could not write.

use std::io::Write as _;
use std::path::PathBuf;
use std::process::ExitCode;

use gandr_surface_diagnostics::Entry;
use gandr_surface_diagnostics::RenderStyle;
use gandr_surface_diagnostics::entries;
use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::Invocation;
use gandr_surface_dispatcher::Outcome;
use gandr_surface_dispatcher::RunVerdict;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Verb;
use gandr_surface_dispatcher::Walk;
use quenchant_shape::shape::Maybe;

/// The exit code of a run with an unsettled declaration.
const UNSETTLED: u8 = 1;

/// The exit code of a fault: the engine's, a path's, the invocation's or the
/// output's.
const FAULTED: u8 = 2;

/// gandr language toolchain driver.
#[derive(Debug, clap::Parser)]
#[command(name = "gandr", version, about)]
#[repr(transparent)]
struct Cli
{
    /// The verb; with none, the driver prints its status.
    #[command(subcommand)]
    command: Option<Command>,
}

/// The driver's verbs.
#[derive(Debug, clap::Subcommand)]
enum Command
{
    /// Check every declaration of the sources under each path.
    ///
    /// Exits 0 when every declaration settles, 1 when one does not, and 2 on
    /// an engine fault or a path that cannot be read.
    Check
    {
        /// Print a declaration unsettled by its obligations alone as a goal,
        /// rather than failing the run.
        #[arg(long)]
        goals: bool,
        /// Source files, and directories searched for `.gandr` sources.
        #[arg(required = true)]
        paths: Vec<PathBuf>,
    },
    /// Run the corpus under each path: the same pass as `check`, printing
    /// every fixture.
    ///
    /// Exits as `check` does.
    Test
    {
        /// Source files, and directories searched for `.gandr` sources.
        #[arg(required = true)]
        paths: Vec<PathBuf>,
    },
}

/// Parse the driver's arguments, route the invocation, render the outcome.
///
/// # Specification
/// - requires: nothing of the caller; the arguments come from the process
///   environment.
/// - ensures: [`Cli`] parses before anything else is written. `--help` and
///   `--version` print and exit `0`; any other argument error prints its usage
///   message and exits `2`. A bare invocation prints one status line and exits
///   `0`. `check` and `test` walk their paths, print what [`render`] prints,
///   and exit `0`, `1` or `2` as the run settled, was unsettled or faulted.
///   Output the driver cannot write is noted on standard error, when that is
///   writable, and exits `2`.
/// - provides: the exit code as the run's verdict. The postcondition stays
///   prose: the exit code and the lines written are effects on the process, not
///   a value this call returns to a caller that could observe them. With
///   `tracing`, a thread-local subscriber reports dispatch spans to standard
///   error after argument parsing.
/// - fails: never by panic or abort; every failure is an exit code.
/// - panics: none. Output goes through locked handles and the fallible
///   `writeln!`, never `println!`, whose write-failure path panics. Clap's
///   command-definition assertions fire only under `debug_assertions`.
///
/// # Adequacy
/// - hypothesis: L2 — the binary is spawned on inputs triggering each exit
///   code, the code and the lines asserted; output to a pipe with no reader is
///   the unwritable case.
/// - witness: `cli::cli::a_settled_run_exits_zero`
/// - witness: `cli::cli::an_unsettled_run_exits_one`
/// - witness: `cli::cli::an_unreadable_path_exits_two`
/// - witness: `cli::cli::a_malformed_invocation_exits_two`
/// - witness: `cli::cli::unwritable_standard_output_exits_two`
/// - witness: `cli::cli::a_bare_invocation_prints_the_status`
fn main() -> ExitCode
{
    let cli = match <Cli as clap::Parser>::try_parse() {
        | Ok(cli) => cli,
        | Err(error) => return usage(&error),
    };
    #[cfg(feature = "tracing")]
    let _subscriber = tracing::subscriber::set_default(
        tracing_subscriber::fmt()
            .with_writer(std::io::stderr)
            .with_span_events(tracing_subscriber::fmt::format::FmtSpan::CLOSE)
            .finish(),
    );
    #[cfg(feature = "tracing")]
    let _span = tracing::info_span!("driver").entered();
    let invocation = match cli.command {
        | None => Invocation::Status,
        | Some(Command::Check { goals, paths }) => Invocation::Check {
            goals: if goals { Goals::Reported } else { Goals::Gated },
            paths,
        },
        | Some(Command::Test { paths }) => Invocation::Test { paths },
    };
    let mut stdout = std::io::stdout().lock();
    let mut stderr = std::io::stderr().lock();
    let rendered = render(
        gandr_surface_dispatcher::dispatch(invocation),
        &mut stdout,
        &mut stderr,
    );
    let flushed = rendered.and_then(|exit| stdout.flush().map(|()| exit));
    match flushed {
        | Ok(exit) => {
            #[cfg(feature = "tracing")]
            tracing::info!("output flushed");
            exit
        },
        | Err(error) => match writeln!(stderr, "gandr: cannot write the output: {error}") {
            // When standard error is unwritable too, the exit code is the one
            // channel left.
            | Ok(()) | Err(_) => ExitCode::from(FAULTED),
        },
    }
}

/// Print clap's message for `error` and choose the exit code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a help or version request prints to standard output and exits
///   `0`; any other argument error prints its usage message to standard error
///   and exits `2`, as does a message that cannot be printed.
/// - provides: the exit of an invocation clap did not accept.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — help, an unknown verb and a verb without paths, each
///   spawned and its exit code asserted.
/// - witness: `cli::cli::a_malformed_invocation_exits_two`
/// - witness: `cli::cli::help_exits_zero`
fn usage(error: &clap::Error) -> ExitCode
{
    match (error.print(), error.use_stderr()) {
        | (Ok(()), false) => ExitCode::SUCCESS,
        | (Ok(()), true) | (Err(_), _) => ExitCode::from(FAULTED),
    }
}

/// Render `outcome` and choose the exit code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the status prints one line naming the driver's version. A walk
///   prints, for each source, what `gandr-surface-diagnostics` renders of its
///   step under the verb: each refusal, unsettled declaration and goal as a
///   plain source snippet followed by an empty line, and each ledger line — a
///   settled fixture or a pending source's refusal under `test`, a pending
///   source the lowering read — prefixed with its path. Each path the walk
///   cannot carry through the pipeline is a line on standard error. The run's
///   report and its verdict close standard output, and the exit code is the
///   verdict's.
/// - provides: the one renderer both verbs share.
/// - fails: the first write error on either stream.
/// - panics: none.
///
/// # Errors
/// The [`std::io::Error`] of the first write that failed.
///
/// # Adequacy
/// - hypothesis: L2 — the binary is spawned on a settled, an unsettled, a
///   goal-only, a pending and an unreadable input under each verb, and the
///   lines and exit code asserted.
/// - witness: `cli::cli::a_settled_run_exits_zero`
/// - witness: `cli::cli::an_unsettled_run_exits_one`
/// - witness: `cli::cli::goals_report_an_obligation_without_failing`
/// - witness: `cli::cli::the_test_verb_prints_every_fixture_and_pending_source`
/// - witness: `cli::cli::an_unreadable_path_exits_two`
fn render(
    outcome: Outcome,
    stdout: &mut dyn std::io::Write,
    stderr: &mut dyn std::io::Write,
) -> std::io::Result<ExitCode>
{
    match outcome {
        | Outcome::Status(report) => {
            writeln!(stdout, "gandr {} — {report}", env!("CARGO_PKG_VERSION"))?;
            Ok(ExitCode::SUCCESS)
        },
        | Outcome::Run { verb, walk } => run(verb, walk, stdout, stderr),
    }
}

/// Walk `walk` under `verb`, printing each step, then the report and the
/// verdict.
///
/// # Specification
/// trivial.
///
/// # Errors
/// The [`std::io::Error`] of the first write that failed.
fn run(
    verb: Verb,
    mut walk: Walk,
    stdout: &mut dyn std::io::Write,
    stderr: &mut dyn std::io::Write,
) -> std::io::Result<ExitCode>
{
    while let Maybe::Present(step) = walk.step() {
        match step {
            | Step::Source { .. } => {
                for entry in entries(&step, verb) {
                    match entry {
                        | Entry::Report(report) => {
                            writeln!(stdout, "{}\n", report.render(RenderStyle::Plain))?;
                        },
                        | Entry::Line(line) => writeln!(stdout, "{line}")?,
                    }
                }
            },
            | Step::Fault { path, fault } => {
                writeln!(stderr, "gandr: {}: {fault}", path.display())?;
            },
        }
    }
    let report = walk.report();
    let verdict = report.verdict(verb);
    writeln!(stdout, "{report}")?;
    writeln!(stdout, "verdict: {verdict}")?;
    Ok(match verdict {
        | RunVerdict::Settled => ExitCode::SUCCESS,
        | RunVerdict::Unsettled => ExitCode::from(UNSETTLED),
        | RunVerdict::Faulted => ExitCode::from(FAULTED),
    })
}
