//! Driver binary for the gandr language toolchain.
//!
//! Installs as `gandr`. The driver owns the argument surface and the process
//! boundary: it parses an invocation, routes it through the surface
//! dispatcher, renders the outcome, and reports the run through its exit
//! code.
//!
//! # Exit codes
//!
//! - `0`: every declaration settled; also `--help`, `--version`, a bare
//!   invocation, `lsp --capabilities`, a language-server session ended by
//!   `exit` after `shutdown`, a read-evaluate loop that reached the end of its
//!   input or `:quit`, a terminal face the user left, and `tui --smoke`.
//! - `1`: at least one declaration is unsettled, or a source was not read as
//!   its root expects; also a language-server session ended before `shutdown`.
//! - `2`: an engine fault, an unreadable source or a path naming none, a
//!   malformed invocation, output the driver could not write, a language-server
//!   stream that failed, a read-evaluate loop or a terminal face stopped by a
//!   fault, or a terminal face asked for without a terminal.

use std::io::IsTerminal as _;
use std::io::Write as _;
use std::path::PathBuf;
use std::process::ExitCode;

use gandr_surface_diagnostics::Entry;
use gandr_surface_diagnostics::RenderStyle;
use gandr_surface_diagnostics::TerminalCapability;
use gandr_surface_diagnostics::entries;
use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::Invocation;
use gandr_surface_dispatcher::Outcome;
use gandr_surface_dispatcher::RunVerdict;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Verb;
use gandr_surface_dispatcher::Walk;
use gandr_surface_lsp::Capabilities;
use gandr_surface_lsp::Served;
use gandr_surface_repl::Ended;
use quenchant_shape::shape::Maybe;

/// The exit code of a run with an unsettled declaration.
const UNSETTLED: u8 = 1;

/// The exit code of a language-server session that ended before `shutdown`.
const ABRUPT: u8 = 1;

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
    /// Serve the Language Server Protocol over standard input and output.
    ///
    /// Exits 0 when `exit` follows `shutdown`, 1 when the session ends
    /// before `shutdown`, and 2 when a stream fails.
    Lsp
    {
        /// Print the capabilities the server advertises, as one line of JSON,
        /// and exit.
        #[arg(long)]
        capabilities: bool,
    },
    /// Run the read-evaluate loop over standard input and output.
    ///
    /// On a terminal, lines are edited with history kept for the session;
    /// piped, each line is read in turn and a plain transcript printed. Exits
    /// 0 at the end of input or `:quit`, and 2 when a fault stops the loop.
    Repl
    {
        /// Print the plain transcript even when standard input is a terminal.
        #[arg(long)]
        batch: bool,
    },
    /// Run the read-evaluate loop full-screen: the transcript, an input pane
    /// and a status line.
    ///
    /// Needs a terminal on standard input and output. Exits 0 when the user
    /// leaves, and 2 when a fault stops the face or no terminal is attached.
    Tui
    {
        /// Run the face once off-screen, print `gandr tui: ready`, and exit.
        #[arg(long)]
        smoke: bool,
    },
}

/// Which face of the read-evaluate loop to run.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Face
{
    /// The plain transcript, whatever standard input is.
    Batch,
    /// The line editor when standard input is a terminal, the plain transcript
    /// otherwise.
    ByInput,
}

/// Where the terminal face draws.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Screen
{
    /// The process's terminal.
    Terminal,
    /// A headless backend, once, for a gate without a terminal.
    Smoke,
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
///   `lsp` serves and `lsp --capabilities` prints as [`lsp`] and
///   [`capabilities`] state, `repl` runs as [`repl`] states, and `tui` as
///   [`tui`] states. Output the driver cannot write is noted on standard error,
///   when that is writable, and exits `2`.
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
/// - witness: `cli::cli::lsp_capabilities_print_one_line_of_json`
/// - witness: `cli::cli::lsp_serves_a_session_over_the_standard_streams`
/// - witness: `cli::cli::a_piped_repl_session_prints_its_transcript`
/// - witness: `cli::cli::the_tui_smoke_face_prints_ready`
/// - witness: `cli::cli::the_tui_needs_a_terminal`
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
        | Some(Command::Lsp {
            capabilities: false,
        }) => return lsp(),
        | Some(Command::Lsp { capabilities: true }) => return capabilities(),
        | Some(Command::Repl { batch }) => {
            return repl(if batch { Face::Batch } else { Face::ByInput });
        },
        | Some(Command::Tui { smoke }) => {
            return tui(if smoke {
                Screen::Smoke
            }
            else {
                Screen::Terminal
            });
        },
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

/// Serve the language server over standard input and output until the
/// session ends, and choose the exit code.
///
/// # Specification
/// - requires: nothing; the streams come from the process.
/// - ensures: every frame the client writes to standard input is answered on
///   standard output by `gandr-surface-lsp`, until `exit` or the input closes;
///   the session exits `0` when it ends after `shutdown` and `1` before it. A
///   stream that fails is noted on standard error, when that is writable, and
///   exits `2`.
/// - provides: the editor's entry point.
/// - fails: never by panic; every failure is an exit code.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the binary is spawned with a whole session on standard
///   input, and with one closed before `shutdown`, and the frames and exit code
///   asserted.
/// - witness: `cli::cli::lsp_serves_a_session_over_the_standard_streams`
fn lsp() -> ExitCode
{
    let mut input = std::io::stdin().lock();
    let mut output = std::io::stdout().lock();
    match gandr_surface_lsp::serve(&mut input, &mut output) {
        | Ok(Served::Clean) => ExitCode::SUCCESS,
        | Ok(Served::Abrupt) => ExitCode::from(ABRUPT),
        | Err(fault) => {
            match writeln!(
                std::io::stderr(),
                "gandr: the language server stopped: {fault}"
            ) {
                // When standard error is unwritable too, the exit code is the
                // one channel left.
                | Ok(()) | Err(_) => ExitCode::from(FAULTED),
            }
        },
    }
}

/// Run the read-evaluate loop on the standard streams, and choose the exit
/// code.
///
/// # Specification
/// - requires: nothing; the streams come from the process.
/// - ensures: under [`Face::Batch`], or when standard input is not a terminal,
///   every line of standard input is offered to the loop and its plain
///   transcript written to standard output; otherwise the line editor reads the
///   terminal, and refusals are coloured when standard output is a terminal
///   too. The loop exits `0` when its input ends or the user quits, and `2`
///   when a fault stops it or its output cannot be written, the fault noted on
///   standard error when that is writable.
/// - provides: `gandr repl`.
/// - fails: never by panic; every failure is an exit code.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the binary is spawned with a session piped on standard
///   input, and its transcript and exit code asserted; the terminal face was
///   exercised by hand on a pseudo-terminal.
/// - witness: `cli::cli::a_piped_repl_session_prints_its_transcript`
fn repl(face: Face) -> ExitCode
{
    let input = std::io::stdin();
    let mut output = std::io::stdout().lock();
    let ended = match (face, input.is_terminal()) {
        | (Face::Batch, _) | (Face::ByInput, false) => {
            gandr_surface_repl::run_batch(input.lock(), &mut output, RenderStyle::Plain)
        },
        | (Face::ByInput, true) => {
            let style = RenderStyle::for_terminal(TerminalCapability::from(output.is_terminal()));
            gandr_surface_repl::run_interactive(&mut output, style)
        },
    };
    let noted = match ended {
        | Ok(Ended::Completed) => return ExitCode::SUCCESS,
        | Ok(Ended::Faulted(fault)) => writeln!(std::io::stderr(), "gandr: {fault}"),
        | Err(error) => writeln!(std::io::stderr(), "gandr: cannot write the output: {error}"),
    };
    match noted {
        // When standard error is unwritable too, the exit code is the one
        // channel left.
        | Ok(()) | Err(_) => ExitCode::from(FAULTED),
    }
}

/// Run the terminal face, or its smoke face, and choose the exit code.
///
/// # Specification
/// - requires: nothing; the streams come from the process.
/// - ensures: under [`Screen::Smoke`], the face runs once off-screen and `gandr
///   tui: ready` is printed on standard output; no terminal is touched. Under
///   [`Screen::Terminal`], with standard input and output both terminals, the
///   face takes the terminal until the user leaves and then restores it;
///   without them nothing is drawn and the missing terminal is noted on
///   standard error. Either face exits `0` when it completes, and `2` when a
///   fault stops it, the terminal fails, its output cannot be written or no
///   terminal is attached, the cause noted on standard error when that is
///   writable.
/// - provides: `gandr tui` and `gandr tui --smoke`.
/// - fails: never by panic; every failure is an exit code.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2 — the binary is spawned under `--smoke` and its line and
///   exit code asserted, under `--smoke` into a closed pipe and its fault
///   asserted, and without a terminal and its refusal asserted; the terminal
///   face was exercised by hand on a pseudo-terminal.
/// - witness: `cli::cli::the_tui_smoke_face_prints_ready`
/// - witness: `cli::cli::the_tui_needs_a_terminal`
/// - witness: `cli::cli::unwritable_standard_output_exits_two`
fn tui(screen: Screen) -> ExitCode
{
    let attached = std::io::stdin().is_terminal() && std::io::stdout().is_terminal();
    let noted = match (screen, attached) {
        | (Screen::Smoke, _) => match gandr_surface_tui::run_smoke(&mut std::io::stdout().lock()) {
            | Ok(Ended::Completed) => return ExitCode::SUCCESS,
            | Ok(Ended::Faulted(fault)) => writeln!(std::io::stderr(), "gandr: {fault}"),
            | Err(error) => writeln!(std::io::stderr(), "gandr: cannot write the output: {error}"),
        },
        | (Screen::Terminal, false) => writeln!(
            std::io::stderr(),
            "gandr: the terminal face needs a terminal on standard input and output; `gandr repl` reads a pipe"
        ),
        | (Screen::Terminal, true) => match gandr_surface_tui::run() {
            | Ok(Ended::Completed) => return ExitCode::SUCCESS,
            | Ok(Ended::Faulted(fault)) => writeln!(std::io::stderr(), "gandr: {fault}"),
            | Err(error) => writeln!(std::io::stderr(), "gandr: the terminal failed: {error}"),
        },
    };
    match noted {
        // When standard error is unwritable too, the exit code is the one
        // channel left.
        | Ok(()) | Err(_) => ExitCode::from(FAULTED),
    }
}

/// Print the capabilities the language server advertises, and choose the exit
/// code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: standard output receives the `initialize` result as one line of
///   JSON and the process exits `0`; output the driver cannot write is noted on
///   standard error, when that is writable, and exits `2`.
/// - provides: what a client or a packager reads without starting a session.
/// - fails: never by panic; every failure is an exit code.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L1 — the binary is spawned and its whole output compared with
///   the line the server crate displays.
/// - witness: `cli::cli::lsp_capabilities_print_one_line_of_json`
fn capabilities() -> ExitCode
{
    let mut stdout = std::io::stdout().lock();
    let written = writeln!(stdout, "{Capabilities}").and_then(|()| stdout.flush());
    match written {
        | Ok(()) => ExitCode::SUCCESS,
        | Err(error) => {
            match writeln!(std::io::stderr(), "gandr: cannot write the output: {error}") {
                | Ok(()) | Err(_) => ExitCode::from(FAULTED),
            }
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
