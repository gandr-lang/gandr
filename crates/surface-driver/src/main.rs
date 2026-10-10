//! Driver binary for the gandr language toolchain.
//!
//! Installs as `gandr`. The driver owns the argument surface and the process
//! boundary: it parses an invocation, routes it through the surface
//! dispatcher, renders the outcome, and reports the run through its exit
//! code.
//!
//! # Exit codes
//!
//! - `0`: every declaration settled, or a script's run returned a value; also
//!   `--help`, `--version`, a bare invocation, `lsp --capabilities`, a
//!   language-server session ended by `exit` after `shutdown`, a read-evaluate
//!   loop that reached the end of its input or `:quit`, a terminal face the
//!   user left, and `tui --smoke`.
//! - `1`: at least one declaration is unsettled, or a source was not read as
//!   its root expects; a script's run was blamed on a goal or stopped short of
//!   a value; also a language-server session ended before `shutdown`.
//! - `2`: an engine fault, an unreadable source or a path naming none, a
//!   malformed invocation, output the driver could not write, a language-server
//!   stream that failed, a read-evaluate loop or a terminal face stopped by a
//!   fault, a terminal face asked for without a terminal, or a script that
//!   never reached the machine.

use std::io::IsTerminal as _;
use std::io::Write as _;
use std::path::PathBuf;
use std::process::ExitCode;

use gandr_surface_diagnostics::Entry;
use gandr_surface_diagnostics::RenderStyle;
use gandr_surface_diagnostics::TerminalCapability;
use gandr_surface_diagnostics::entries;
use gandr_surface_dispatcher::Evaluation;
use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::Invocation;
use gandr_surface_dispatcher::Outcome;
use gandr_surface_dispatcher::Ran;
use gandr_surface_dispatcher::RunStatus;
use gandr_surface_dispatcher::RunVerdict;
use gandr_surface_dispatcher::Script;
use gandr_surface_dispatcher::ScriptRun;
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

/// The exit code of a script whose run reached the machine and stopped short
/// of a value: blamed on a goal, stuck or unfinished.
const STOPPED: u8 = 1;

/// The exit code of a fault: the engine's, a path's, the invocation's or the
/// output's.
const FAULTED: u8 = 2;

/// The exit code of a script that never reached the machine.
const UNREACHED: u8 = 2;

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
    /// Run a source as a program: check it as `check` does, then run its last
    /// declaration and print the value.
    ///
    /// Exits 0 when the run returns a value, 1 when it is blamed on a goal or
    /// stops short of one, and 2 when the source never reaches the machine.
    Run
    {
        /// The source file to run.
        path: PathBuf,
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
///   and exit `0`, `1` or `2` as the run settled, was unsettled or faulted;
///   `run` runs its script as [`script`] states. `lsp` serves and `lsp
///   --capabilities` prints as [`lsp`] and [`capabilities`] state, `repl` runs
///   as [`repl`] states, and `tui` as [`tui`] states. Output the driver cannot
///   write is noted on standard error, when that is writable, and exits `2`.
/// - provides: the exit code as the run's verdict. With `tracing`, a
///   thread-local subscriber reports dispatch spans to standard error after
///   argument parsing.
/// - fails: never by panic or abort; every failure is an exit code.
/// - panics: none. Output goes through locked handles and the fallible
///   `writeln!`, never `println!`, whose write-failure path panics. Clap's
///   command-definition assertions fire only under `debug_assertions`.
///
/// # Adequacy
/// - hypothesis: L2/L3 — finite settled, refused, owed, missing and malformed
///   inputs exercise each process status and stream role. Closed output pipes
///   distinguish swallowed writes; protocol sessions distinguish completion
///   from abrupt termination. Misrouting, wrong severity and reordered output
///   change these observations. Arbitrary terminal environments and tracing
///   presentation are outside the subprocess domain.
/// - witness: `cli::cli::a_settled_run_exits_zero`
/// - witness: `cli::cli::an_unsettled_run_exits_one`
/// - witness: `cli::cli::an_unreadable_path_exits_two`
/// - witness: `cli::cli::a_malformed_invocation_exits_two`
/// - witness: `cli::cli::unwritable_standard_output_exits_two`
/// - witness: `cli::cli::status_and_version_identify_the_same_build`
/// - witness: `cli::cli::lsp_serves_a_session_over_the_standard_streams`
/// - witness: `cli::cli::a_piped_repl_session_prints_its_transcript`
/// - witness: `cli::cli::smoke_is_terminal_free_but_interactive_tui_refuses_pipes`
/// - witness: `cli::cli::a_script_that_returns_a_value_leaves_successfully`
/// - witness: `cli::cli::a_script_that_blames_leaves_with_a_failure_status`
/// - witness: `cli::cli::an_ill_typed_script_is_refused_by_the_checker`
#[anodized::spec(ensures: |ret| ret == ExitCode::SUCCESS || ret == ExitCode::from(UNSETTLED) || ret == ExitCode::from(FAULTED))]
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
        | Some(Command::Run { path }) => Invocation::Run { path },
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
/// - ensures: client frames are fed to `gandr-surface-lsp` and its protocol
///   responses written to standard output until exit or EOF; notifications do
///   not acquire request replies. A session exits `0` after shutdown and `1`
///   before it. A failed stream is noted on standard error when writable and
///   exits `2`.
/// - provides: the editor's entry point.
/// - fails: never by panic; every failure is an exit code.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2/L3 — initialize/shutdown/exit, premature EOF and a
///   truncated frame are observed as protocol output and exit codes. Wrong
///   framing, lost replies and collapsed clean/abrupt/fault statuses change
///   these traces. Arbitrary methods and live-editor timing are excluded.
/// - witness: `cli::cli::lsp_serves_a_session_over_the_standard_streams`
#[anodized::spec(ensures: |ret| ret == ExitCode::SUCCESS || ret == ExitCode::from(ABRUPT) || ret == ExitCode::from(FAULTED))]
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
/// - hypothesis: L2/L3 — a piped load, type query, refused declaration and quit
///   leave exact transcript rows and an unread suffix; explicit batch agrees
///   with pipe selection. Wrong routing, failure classification or reads past
///   quit change the observations. Interactive editing and terminal colour
///   appearance are outside these finite pipe sessions.
/// - witness: `cli::cli::a_piped_repl_session_prints_its_transcript`
#[anodized::spec(ensures: |ret| ret == ExitCode::SUCCESS || ret == ExitCode::from(FAULTED))]
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
/// - hypothesis: L2/L3 — headless launch into a closed pipe and terminal launch
///   without an attached terminal expose failure status and stream routing.
///   Success/failure confusion, swallowed output errors or terminal escape
///   leakage change the observations. Real terminal restoration is outside
///   these subprocess fixtures and is exercised by the smoke run.
/// - witness: `cli::cli::smoke_is_terminal_free_but_interactive_tui_refuses_pipes`
/// - witness: `cli::cli::unwritable_standard_output_exits_two`
#[anodized::spec(ensures: |ret| ret == ExitCode::SUCCESS || ret == ExitCode::from(FAULTED))]
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
/// - hypothesis: L3 — a closed output pipe observes write refusal and exit
///   status. A swallowed write failure or success status changes the result.
///   The successful JSON surface is exercised by the command smoke; protocol
///   capability contents belong to the server rather than this adapter.
/// - witness: `cli::cli::unwritable_standard_output_exits_two`
#[anodized::spec(ensures: |ret| ret == ExitCode::SUCCESS || ret == ExitCode::from(FAULTED))]
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
/// - hypothesis: L3 — help, version, an unknown verb, missing paths and closed
///   output pipes expose status and output-stream choice. Accepting malformed
///   arguments, wrong destinations and swallowed writes change those finite
///   observations. Localized usage wording is outside them.
/// - witness: `cli::cli::a_malformed_invocation_exits_two`
/// - witness: `cli::cli::help_exits_zero`
/// - witness: `cli::cli::unwritable_standard_output_exits_two`
/// - witness: `cli::cli::status_and_version_identify_the_same_build`
#[anodized::spec(ensures: |ret| ret == ExitCode::from(FAULTED)
    || (!error.use_stderr() && ret == ExitCode::SUCCESS))]
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
///   verdict's. A script follows [`script`]: its value goes to standard output,
///   its diagnostics to standard error and its run status chooses the exit.
/// - provides: the one renderer every verb that reports through the dispatcher
///   shares.
/// - fails: the first write error on either stream.
/// - panics: none.
///
/// # Errors
/// The [`std::io::Error`] of the first write that failed.
///
/// # Adequacy
/// - hypothesis: L2/L3 — settled, refused, owed, pending and unreadable sources
///   expose report selection and status precedence under both verbs. Missing
///   diagnostics, ledger leakage or fault demotion changes the observations.
///   Arbitrary source programs and output devices are excluded.
/// - witness: `cli::cli::a_settled_run_exits_zero`
/// - witness: `cli::cli::an_unsettled_run_exits_one`
/// - witness: `cli::cli::goals_report_an_obligation_without_failing`
/// - witness: `cli::cli::the_test_verb_prints_every_fixture_and_pending_source`
/// - witness: `cli::cli::an_unreadable_path_exits_two`
/// - witness: `cli::cli::a_failed_diagnostic_stream_stops_later_output`
#[anodized::spec(captures: [status = matches!(outcome, Outcome::Status(_))],
    ensures: |ref ret| ret.as_ref().map_or(true, |exit|
        (*exit == ExitCode::SUCCESS || *exit == ExitCode::from(UNSETTLED) || *exit == ExitCode::from(FAULTED))
            && (!status || *exit == ExitCode::SUCCESS)))]
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
        | Outcome::Script(mut runnable) => script(&mut runnable, stdout, stderr),
    }
}

/// Walk `walk` under `verb`, printing each step, then the report and the
/// verdict.
///
/// # Specification
/// - requires: nothing.
/// - ensures: consumes the walk, writing source reports and ledger entries to
///   standard output and path faults to standard error, then the final report
///   and verdict. The exit is zero for settled, one for unsettled and two for
///   faulted, as the walk's final report decides under the offered verb.
/// - provides: ordered rendering and severity aggregation for check and test.
/// - fails: the first write error, without attempting subsequent entries.
/// - panics: none.
///
/// # Errors
/// The [`std::io::Error`] of the first write that failed.
///
/// # Adequacy
/// - hypothesis: L2/L3 — mixed settled, refused and unreadable paths and
///   fixture/pending roots expose continuation, stream separation and fault
///   precedence. Missing sources, reordered severity or wrong ledger selection
///   changes exact counts and statuses. Arbitrary filesystems are excluded.
/// - witness: `cli::cli::an_unreadable_path_exits_two`
/// - witness: `cli::cli::the_test_verb_prints_every_fixture_and_pending_source`
/// - witness: `cli::cli::a_failed_diagnostic_stream_stops_later_output`
#[anodized::spec(ensures: |ref ret| ret.as_ref().map_or(true, |exit| *exit == match walk.report().verdict(verb) {
    RunVerdict::Settled => ExitCode::SUCCESS,
    RunVerdict::Unsettled => ExitCode::from(UNSETTLED),
    RunVerdict::Faulted => ExitCode::from(FAULTED),
}))]
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

/// Run `runnable`, printing its value on standard output and everything else
/// on standard error, and choose the exit code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a path that cannot be read as one source is `gandr: <path>:
///   <fault>` on standard error. Otherwise every report `gandr check --goals`
///   prints for the source goes to standard error as a plain snippet followed
///   by an empty line, and every ledger line beside them; then a run that
///   returned a value writes the value as the one line of standard output. A
///   run blamed, stuck or unfinished, and a target that reaches a declaration
///   the machine carries no image of, is one line on standard error: `gandr:`,
///   the path, the target's name in backticks and the evaluation's spelling. A
///   source carrying a refusal is `gandr: <path>: refused; nothing ran` and one
///   declaring no name `gandr: <path>: declares no name to run`, each on
///   standard error. The exit code is `0` for a value, `1` for a run that
///   stopped short of one, and `2` for a script that never reached the machine.
/// - provides: `gandr run`, with its value on the one stream a caller reads.
/// - fails: the first write error on either stream.
/// - panics: none.
///
/// # Errors
/// The [`std::io::Error`] of the first write that failed.
///
/// # Adequacy
/// - hypothesis: L3 — value, blame, type refusal, unrelated declaration
///   refusal, absent source and empty program are observed through exact
///   status, value multiplicity and separate diagnostic streams. Wrong status,
///   repeated values or evaluation after refusal changes these observations.
///   Arbitrary machine programs and interruption timing are outside them.
/// - witness: `cli::cli::a_script_that_returns_a_value_leaves_successfully`
/// - witness: `cli::cli::a_script_that_blames_leaves_with_a_failure_status`
/// - witness: `cli::cli::an_ill_typed_script_is_refused_by_the_checker`
/// - witness: `cli::cli::an_outcome_only_refusal_is_visible_in_a_script_run`
/// - witness: `cli::cli::an_absent_script_is_refused_by_path`
/// - witness: `cli::cli::a_script_with_no_program_is_refused`
/// - witness: `cli::cli::the_value_of_a_run_is_printed_once`
/// - witness: `cli::cli::a_failed_diagnostic_stream_stops_later_output`
#[anodized::spec(ensures: |ref ret| ret.as_ref().map_or(true, |exit|
    *exit == ExitCode::SUCCESS || *exit == ExitCode::from(STOPPED) || *exit == ExitCode::from(UNREACHED)))]
fn script(
    runnable: &mut Script,
    stdout: &mut dyn std::io::Write,
    stderr: &mut dyn std::io::Write,
) -> std::io::Result<ExitCode>
{
    let ran = runnable.run();
    let status = ran.status();
    match ran {
        | ScriptRun::Fault { path, fault } => {
            writeln!(stderr, "gandr: {}: {fault}", path.display())?;
        },
        | ScriptRun::Source { step, ran } => {
            for entry in entries(&step, Verb::Check(Goals::Reported)) {
                match entry {
                    | Entry::Report(report) => {
                        writeln!(stderr, "{}\n", report.render(RenderStyle::Plain))?;
                    },
                    | Entry::Line(line) => writeln!(stderr, "{line}")?,
                }
            }
            let path = match step {
                | Step::Source { path, .. } | Step::Fault { path, .. } => path.display(),
            };
            match ran {
                | Ran::Evaluated {
                    evaluation: Evaluation::Value(value),
                    ..
                } => writeln!(stdout, "{value}")?,
                | Ran::Evaluated { target, evaluation } => {
                    writeln!(stderr, "gandr: {path}: `{target}` {evaluation}")?;
                },
                | Ran::Refused => writeln!(stderr, "gandr: {path}: refused; nothing ran")?,
                | Ran::NoProgram => writeln!(stderr, "gandr: {path}: declares no name to run")?,
            }
        },
    }
    Ok(match status {
        | RunStatus::Value => ExitCode::SUCCESS,
        | RunStatus::Failed => ExitCode::from(STOPPED),
        | RunStatus::Unreached => ExitCode::from(UNREACHED),
    })
}
