//! Driver binary for the gandr language toolchain.
//!
//! Installs as `gandr`. The driver owns the argument surface and the process
//! boundary: it parses an invocation, routes it through the surface
//! dispatcher, renders the outcome, and reports the run through its exit
//! code.
//!
//! # Exit codes
//!
//! | Code | Meaning |
//! | ---- | ------- |
//! | `0` | every declaration settled, a script's run returned a value, every staged certificate was readmitted, or every source was laid out; also `--help`, `--version`, a bare `gandr`, `gandr lsp --capabilities`, a language-server session ended by `exit` after `shutdown`, a Model Context Protocol session whose input ended, an engine hub that lingered out or found another serving its socket, a read-evaluate loop that reached the end of its input or `:quit`, a terminal face the user left, and `gandr tui --smoke` |
//! | `1` | at least one declaration is unsettled, or a source was not read as its root expects; a script's run was blamed on a goal or stopped short of a value; the kernel refused a staged certificate; `gandr fmt --check` found a source out of layout; also a language-server session ended by `exit`, or by its input closing, before `shutdown` |
//! | `2` | an engine fault, an unreadable path or one naming no source, a malformed invocation, output the driver could not write, a language-server or Model Context Protocol stream that failed, an engine hub that could not be reached, bound or served, a fault that stopped a read-evaluate loop or a terminal face, a terminal that failed, `gandr tui` without a terminal, a script that never reached the machine: unreadable, refused, declaring no name, or running into a declaration the machine carries no image of, or a staged program that could not be checked, a family admission that faulted, or a worker pool that did not start, or a source the formatter refused or could not write back |
//!
//! A fault outranks an unsettled declaration: a run with both exits `2`. The
//! walk continues past a faulted path, so every fault of a run is printed.
//!
//! # Verbs
//!
//! | Invocation | Prints | Fails on |
//! | ---------- | ------ | -------- |
//! | `gandr check <paths>` | each unsettled declaration, each source refused as a whole | any unsettled declaration |
//! | `gandr check --goals <paths>` | as `check`, a declaration unsettled by its obligations alone marked `goal:` | any unsettled declaration but those |
//! | `gandr check --jobs <threads> <paths>` | as `check`, its sources parsed and lowered on that many threads | as `check` |
//! | `gandr check --verbosity <level> <paths>` | as `check`, each report at `user` (the default), `detailed` (adding its class, the producer's wording and the offending source text), `debug` (adding byte spans and the producer's refusal) or `json` (each report, ledger line and the run's summary as one line of JSON); `test` takes the flag too | as `check` |
//! | `gandr test <paths>` | as `check`, plus every fixture, settled or not, and every pending source's refusal | as `check` |
//! | `gandr run <file>` | the value, alone, on standard output; every report `check --goals` would print, and why a run stopped or never started, on standard error | a run blamed or stuck, or a source that never reached the machine |
//! | `gandr stage <programs>` | a line per program — the certificates the kernel readmitted and its families by how they were admitted — then the run's digest and verdict | a certificate the kernel refused, a program that could not be checked, or a family admission that faulted |
//! | `gandr stage --jobs <threads> <programs>` | as `stage`, each program's stages forked onto that many threads | as `stage` |
//! | `gandr fmt <paths>` | the path of each source whose layout changed, written back over it | a path that cannot be read or written back, names no source, or holds a source the formatter refuses |
//! | `gandr fmt --check <paths>` | the path of each source out of layout; nothing is written | as `fmt`, and any source out of layout |
//! | `gandr fmt --width <columns> <paths>` | as `fmt`, laid out at that page width instead of 100 | as `fmt` |
//! | `gandr fmt --jobs <threads> <paths>` | as `fmt`, its sources laid out on that many threads | as `fmt` |
//! | `gandr lsp` | the language server's frames on standard output, until `exit`, served by the workspace's hub on Unix | a session ended before `shutdown` |
//! | `gandr lsp --standalone` | as `lsp`, served in its own process | as `lsp` |
//! | `gandr lsp --socket <path> --linger-ms <ms>` | as `lsp`, through the hub on that socket, a hub it starts lingering that long | as `lsp` |
//! | `gandr lsp --capabilities` | the `initialize` result as one line of JSON | nothing |
//! | `gandr mcp` | the Model Context Protocol server's lines on standard output, until standard input ends, served by the workspace's hub (Unix) | a stream that failed or a hub it could not reach |
//! | `gandr mcp --socket <path> --linger-ms <ms>` | as `mcp`, through the hub on that socket, a hub it starts lingering that long | as `mcp` |
//! | `gandr view` | the cards of the document the workspace's hub checked last, full-screen on a terminal; piped, each report's rows then a blank line (Unix) | a stream that failed, a line that is not a frame, or a hub it could not reach |
//! | `gandr view --socket <path> --linger-ms <ms>` | as `view`, through the hub on that socket, a hub it starts lingering that long | as `view` |
//! | `gandr serve` | each client's timing lines on standard error, until no client has connected for a minute | a socket it cannot bind or serve |
//! | `gandr serve --socket <path> --linger-ms <ms>` | as `serve`, on that socket, lingering that long | as `serve` |
//! | `gandr repl` | the line editor's prompt on a terminal; piped, each submission's echo and its lines, as a plain transcript | a fault that stops the loop |
//! | `gandr repl --batch` | the plain transcript, even on a terminal | as `repl` |
//! | `gandr tui` | the transcript, an input pane and a status line, full-screen on the terminal | a fault that stops the face, a terminal that fails, or no terminal |
//! | `gandr tui --smoke` | `gandr tui: ready` | a fault that stops the face |
//!
//! A path is a source file of any name, or a directory searched for `.gandr`
//! sources. The directories a source sits in decide its root — `strict`,
//! `fixture`, or `fixture/pending` — and a source under none is strict
//! (`gandr-surface-dispatcher`'s `root` module). A refusal, an unsettled
//! declaration and a goal each print as a located source snippet — the class
//! and message, the path with line and column, the lines the report covers with
//! their marks — followed by a blank line (`gandr-surface-diagnostics`'s
//! `report` module); a settled fixture, a pending source's refusal and a
//! pending source the lowering reads each print one ledger line, `<path>:
//! <report>`. The driver writes plain text, without colour. Each fault is
//! `gandr: <path>: <fault>` on standard error. Every run closes standard output
//! with the runner's report — the sources read by root, the lowerings, the
//! goals, the exercised table, the ledger size, the declaration and fixture
//! counts, the surviving obligations, the refusals by class, the run's
//! settlement and its seal — and `verdict: settled`, `unsettled` or `faulted`.
//!
//! `check` and `test` parse and lower their sources on `--jobs` threads (`-j`),
//! or `GANDR_JOBS` when the flag is absent, or else the host's physical
//! performance cores; `1` reads, parses and judges one source at a time. Every
//! byte either stream carries, and the exit, are the same at every count: the
//! sources are judged and printed in walk order whatever thread lowered them
//! (`gandr-surface-dispatcher`'s `walk` module). A count of `0` is a malformed
//! invocation.
//!
//! `gandr run` takes exactly one path, `-` among them: there is no
//! standard-input face for it to name. The source is composed under the root
//! its path classifies as and runs only when no declaration of it was refused;
//! its target is the last name it declares (`gandr-surface-dispatcher`'s
//! `evaluate` module). A completed run writes its value as the one line of
//! standard output, spelled as a `runs` expectation states it, so a caller
//! reads the value without parsing anything else. A run blamed on a goal, stuck
//! or unfinished is `` gandr: <path>: `<target>` <what it came to> `` on
//! standard error; a source carrying a refusal is `gandr: <path>: refused;
//! nothing ran` after its reports, and one declaring no name `gandr: <path>:
//! declares no name to run`.
//!
//! `gandr stage` takes one or more programs, each spelled `pow:LO..HI` or
//! `double:LO..HI` with both exponents inclusive: `pow` specializes the staged
//! power at every exponent in the range against a quoted variable, `double` the
//! doubled iterator at every exponent against the quoted inputs two and three.
//! Each program is checked in order on `--jobs` threads (`-j`), or
//! `GANDR_JOBS`, or the host's physical performance cores, on one work-stealing
//! pool (`gandr-surface-dispatcher`'s `stage` module). Its line is `<spelling>:
//! <r> of <n> certificates readmitted; <f> families:` and the count admitted,
//! partial, plain, refused, over the work bound and faulted, or `<spelling>:
//! <fault>` when it could not be checked. `digest:` and sixteen hexadecimal
//! digits name the merged syntax, certificates, readmissions and family
//! admissions of every program, so a reader compares runs without comparing
//! arenas; `verdict:` is `readmitted`, `refused` or `faulted`. Every byte and
//! the exit are the same at every count. A pool that does not start is `gandr:
//! the worker pool did not start: <error>` on standard error.
//!
//! `gandr fmt` reaches its paths as `check` does and lays out each source
//! through `gandr-surface-format`, which keeps every token and comment, copies
//! strings, shell blocks, holes and repaired forms as written, and refuses any
//! layout whose parse differs from the source's (`gandr-surface-format`). Its
//! sources are laid out on `--jobs` threads as `check`'s are, and every byte
//! either stream carries, every source rewritten and the exit are the same at
//! every count (`gandr-surface-dispatcher`'s `format` module). A source already
//! in layout is not touched; a source the formatter refuses stays as written
//! and is `gandr: <path>: not formatted: <why>` on standard error, and the
//! formatting continues past it. A fault outranks a source out of layout:
//! `gandr fmt --check` over both exits `2`.
//!
//! `gandr lsp` reads frames from standard input and writes every answer and
//! notification to standard output; it rechecks a document whole at every
//! synchronisation and publishes the same reports `gandr check --goals` prints
//! for it, under the root its path classifies as (`gandr-surface-lsp`). Every
//! `gandr lsp` started in one directory reaches one hub, so two editors on a
//! workspace share its open documents. A stream that fails is `gandr: the
//! language server stopped: <fault>` on standard error; a hub that cannot be
//! reached, bound or served is `gandr: the engine hub: <error>`.
//!
//! `gandr mcp` reads one JSON-RPC message per line from standard input and
//! writes each answer and notification as a line to standard output, through
//! the same hub: its tools and resources read the documents the workspace's
//! editors hold open, at the version they last synchronised, so a model sees
//! the diagnostics the editor shows (`gandr-surface-mcp`). A model host runs it
//! as a stdio server in the workspace's directory.
//!
//! `gandr view` attaches to the same hub's render bus and follows the document
//! it checked last: a heading naming the document, its version and how many
//! diagnostics and holes it carries, then each diagnostic at its one-based row
//! and column with its derivation, then each hole with its goal
//! (`gandr-surface-tui`). On a terminal it takes the screen until `q`, Esc or
//! Ctrl-C; piped, each report prints as its rows and a blank line. A view that
//! cannot read the hub's frames ends with `gandr: the view: <cause>` on
//! standard error.
//!
//! `gandr repl` reads declarations a line at a time and submits each buffer the
//! parser reads as complete, judging it with every declaration kept before it,
//! as `gandr check --goals` judges a strict source; a refused submission is
//! shown and not kept. Each submission prints its echo after `▸`, a `name : T`
//! line per declaration it checked followed by what running it came to — `=
//! value`, `! blame`, or `·` and why it stopped or never ran — a `? name : T`
//! line per goal, and each refusal as `gandr check` prints it — in colour only
//! when the line editor runs and standard output is a terminal, plain
//! otherwise. `:type <expression>`, `:load <file>`, `:reset`, `:help` and
//! `:quit` speak to the loop (`gandr-surface-repl`). A fault that stops the
//! loop is `gandr: <fault>` on standard error.
//!
//! `gandr tui` takes the terminal for the same loop: the transcript keeps the
//! lines `gandr repl` prints, coloured by kind with the echo highlighted, above
//! the line being edited; Enter submits, Ctrl-C drops the line and any waiting
//! buffer, and Esc or `:quit` leaves and restores the terminal
//! (`gandr-surface-tui`). Without a terminal on standard input and output it
//! draws nothing and notes `gandr: the terminal face needs a terminal on
//! standard input and output` on standard error; `gandr tui --smoke` needs
//! none. A fault that stops the face is `gandr: <fault>`, and a terminal that
//! fails `gandr: the terminal failed: <error>`, on standard error.
//!
//! # Output the driver cannot write is a fault
//!
//! `main` returns its exit code rather than a `Result`, so a write or flush
//! that fails — a closed pipe, a full disk — is noted on standard error, when
//! that is writable, and exits `2`, the code every fault shares. The runtime
//! ignores `SIGPIPE`, so a reader that closed early surfaces as a failed write,
//! not a signal. The alternative was returning the I/O error from `main`, whose
//! runtime path exits `1` and would read as an unsettled run. The choice
//! reverses if a fault class needs its own code, which would be a fourth row
//! above.
//!
//! # Tests and their limits
//!
//! Driver routing, rendering and nontrivial test helpers carry executable
//! predicates and bounded adequacy arguments. Exit-code domains are checked on
//! each call; the width witness compares every byte of both streams, and the
//! exit, of a run at several thread counts with the serial run's. The global
//! allocator's items are the one executable exemption (the `allocator` module).
//! The predicates do not observe opaque output streams: the CLI witnesses
//! observe exit status, protocol framing, diagnostic identity and location,
//! stream separation, and value multiplicity instead of incidental English
//! wording or a copy of the producer's formatter.
//!
//! `scratch_ownership_keeps_simultaneous_cases_independent` runs two same-name
//! sources in separate roots, removes one root and checks that the other still
//! behaves independently. `a_failed_diagnostic_stream_stops_later_output`
//! closes the diagnostic reader and verifies that neither a later summary nor a
//! script value is emitted after that first write fails. Closed standard output
//! covers status, check, run, help, capabilities, batch REPL and TUI smoke; a
//! literal `-` is checked both absent and present in an owned directory.
//!
//! The native command smoke additionally compares independently decoded LSP
//! initialization and capability JSON, exercises script and batch entry points,
//! and submits a declaration on a terminal before quitting and comparing its
//! terminal settings. These finite observations do not claim arbitrary editor
//! timing, terminal backends, source programs or failing filesystem coverage.
//!
//! The exit-code witnesses are
//! `cli::cli::a_script_that_returns_a_value_leaves_successfully` (exit `0`,
//! `42` alone on standard output),
//! `cli::cli::a_script_that_blames_leaves_with_a_failure_status` (exit `1`) and
//! `cli::cli::an_ill_typed_script_is_refused_by_the_checker` (exit `2`);
//! `cli::cli::the_value_of_a_run_is_printed_once` asserts the value is the
//! whole of standard output.
//!
//! # Optional tracing
//!
//! Build with `cargo build -p gandr-lang --features tracing` to report driver
//! and dispatcher diagnostics on stderr. The feature forwards to
//! `gandr-surface-dispatcher`; this driver has no evaluator dependency and does
//! not activate evaluator tracing. A default build carries no tracing
//! instrumentation or dependency: `cargo tree -p gandr-lang -e normal,build`
//! lists neither `tracing` nor `tracing-subscriber` until the feature is on.
//!
//! Argument parsing runs before subscriber installation, so help, version and
//! argument errors retain their ordinary output. A scoped, thread-local
//! subscriber reports dispatch-span completion and successful output flushing,
//! then restores the prior subscriber when the invocation ends. Libraries
//! install no subscriber. Standard-output write and flush errors remain faults
//! rather than successful-completion events. Tracing diagnostics may precede a
//! fault’s `gandr:` line on stderr; stdout and exit codes are unchanged.
//!
//! The output backend is
//! [`tracing-subscriber`](https://docs.rs/tracing-subscriber/0.3.23/tracing_subscriber/fmt/index.html)
//! 0.3.23 with only `fmt` and its required registry/std support. ANSI
//! formatting, the log bridge, filter parsing, JSON and time integrations stay
//! off. This release includes the [ANSI-input escaping
//! fix](https://rustsec.org/advisories/RUSTSEC-2025-0055); the current events
//! contain fixed messages and no user payloads. A global subscriber was
//! rejected because the invocation need not own process-wide diagnostics; an
//! environment filter adds parsing machinery for no current CLI option. Revisit
//! those choices when the driver gains a consumer requiring them, or the
//! selected version needs a security or maintenance replacement.

use core::num::NonZeroUsize;
use core::ops::ControlFlow;
#[cfg(unix)]
use core::time::Duration;
use std::io::IsTerminal as _;
use std::io::Write as _;
use std::path::PathBuf;
use std::process::ExitCode;
#[cfg(unix)]
use std::time::Instant;

use anodized::spec;
use gandr_surface_diagnostics::Entry;
use gandr_surface_diagnostics::RenderStyle;
use gandr_surface_diagnostics::TerminalCapability;
use gandr_surface_diagnostics::Verbosity;
use gandr_surface_diagnostics::entries;
use gandr_surface_dispatcher::Evaluation;
use gandr_surface_dispatcher::FormatStep;
use gandr_surface_dispatcher::Formatting;
use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::Invocation;
use gandr_surface_dispatcher::Outcome;
use gandr_surface_dispatcher::ProgramSpec;
use gandr_surface_dispatcher::Ran;
use gandr_surface_dispatcher::Rewrite;
use gandr_surface_dispatcher::RunStatus;
use gandr_surface_dispatcher::RunVerdict;
use gandr_surface_dispatcher::Script;
use gandr_surface_dispatcher::ScriptRun;
use gandr_surface_dispatcher::StageVerdict;
use gandr_surface_dispatcher::Staging;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Threads;
use gandr_surface_dispatcher::Verb;
use gandr_surface_dispatcher::Walk;
use gandr_surface_dispatcher::Width;
use gandr_surface_format::FormatOptions;
use gandr_surface_format::PageWidth;
use gandr_surface_lsp::Capabilities;
use gandr_surface_lsp::Served;
use gandr_surface_repl::Ended;
#[cfg(unix)]
use quenchant_shape::shape::Maybe;

mod allocator;

/// The process's global allocator: the private malloc zone of
/// [`allocator::zone::Zone`] on macOS under `malloc-zone`, the system
/// allocator otherwise.
#[cfg(all(feature = "malloc-zone", target_os = "macos"))]
#[global_allocator]
static ALLOCATOR: allocator::zone::Zone = allocator::zone::Zone;

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

/// The exit code of a staged run whose certificate the kernel refused.
const REFUSED: u8 = 1;

/// The exit code of `fmt --check` over a source out of layout.
const UNFORMATTED: u8 = 1;

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
        /// How much of each report to print.
        #[arg(long, value_enum, default_value_t = Level::User)]
        verbosity: Level,
        /// The threads the sources are parsed and lowered on.
        #[command(flatten)]
        jobs: Jobs,
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
        /// How much of each report to print.
        #[arg(long, value_enum, default_value_t = Level::User)]
        verbosity: Level,
        /// The threads the sources are parsed and lowered on.
        #[command(flatten)]
        jobs: Jobs,
        /// Source files, and directories searched for `.gandr` sources.
        #[arg(required = true)]
        paths: Vec<PathBuf>,
    },
    /// Serve the Language Server Protocol over standard input and output.
    ///
    /// On Unix the session is carried to the engine hub serving the current
    /// directory's workspace, started when none runs, so every client of one
    /// workspace shares its open documents. Exits 0 when `exit` follows
    /// `shutdown`, 1 when the session ends before `shutdown`, and 2 when a
    /// stream fails or no hub can be reached.
    Lsp
    {
        /// Print the capabilities the server advertises, as one line of JSON,
        /// and exit.
        #[arg(long)]
        capabilities: bool,
        /// Serve in this process, sharing nothing with other clients.
        #[cfg(unix)]
        #[arg(long)]
        standalone: bool,
        /// The hub's socket, rather than the one the current directory names.
        #[cfg(unix)]
        #[arg(long, value_name = "PATH", conflicts_with = "standalone")]
        socket: Option<PathBuf>,
        /// How long a hub this client starts waits for a client, once its
        /// last has left, before it exits. Defaults to a minute.
        #[cfg(unix)]
        #[arg(long, value_name = "MILLISECONDS", conflicts_with = "standalone")]
        linger_ms: Option<u64>,
    },
    /// Run the engine hub: serve the Language Server Protocol to every editor
    /// of one workspace, and the Model Context Protocol to every model, over
    /// one Unix socket, all of them sharing the documents the editors open.
    ///
    /// `gandr lsp` and `gandr mcp` start one when none runs. Exits 0 when the
    /// hub has had no client for its linger or another hub already serves the
    /// socket, and 2 when the socket cannot be bound or served.
    #[cfg(unix)]
    Serve
    {
        /// The socket to serve, rather than the one the current directory
        /// names.
        #[arg(long, value_name = "PATH")]
        socket: Option<PathBuf>,
        /// How long to wait for a client, once the last has left, before
        /// exiting. Defaults to a minute.
        #[arg(long, value_name = "MILLISECONDS")]
        linger_ms: Option<u64>,
    },
    /// Serve the Model Context Protocol over standard input and output: tools
    /// and resources reading the documents the workspace's editors hold open.
    ///
    /// The session is carried to the engine hub serving the current
    /// directory's workspace, started when none runs. Exits 0 when the client
    /// closes its input and the hub has answered, and 2 when a stream fails or
    /// no hub can be reached.
    #[cfg(unix)]
    Mcp
    {
        /// The hub's socket, rather than the one the current directory names.
        #[arg(long, value_name = "PATH")]
        socket: Option<PathBuf>,
        /// How long a hub this client starts waits for a client, once its
        /// last has left, before it exits. Defaults to a minute.
        #[arg(long, value_name = "MILLISECONDS")]
        linger_ms: Option<u64>,
    },
    /// Follow the document the engine hub checked last: its diagnostics, each
    /// at its row and column with its derivation, and its holes, beside the
    /// editor that shows the text.
    ///
    /// Attaches to the render bus of the hub serving the current directory's
    /// workspace, started when none runs. On a terminal the view takes the
    /// screen until Esc; piped, each report prints as plain rows. Exits 0 when
    /// the user leaves or the hub closes the bus, and 2 when a stream fails,
    /// a line from the hub is not a frame, or no hub can be reached.
    #[cfg(unix)]
    View
    {
        /// The hub's socket, rather than the one the current directory names.
        #[arg(long, value_name = "PATH")]
        socket: Option<PathBuf>,
        /// How long a hub this client starts waits for a client, once its
        /// last has left, before it exits. Defaults to a minute.
        #[arg(long, value_name = "MILLISECONDS")]
        linger_ms: Option<u64>,
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
    /// Check staging observer programs: build each, normalize every source,
    /// readmit every certificate and admit every family through one memo.
    ///
    /// Prints one line per program, then the run's digest and verdict, the
    /// same at every width. Exits 0 when the kernel readmits every
    /// certificate, 1 when it refuses one, and 2 when a program cannot be
    /// checked.
    Stage
    {
        /// The threads each program's stages fork onto.
        #[command(flatten)]
        jobs: Jobs,
        /// The programs, in order: `pow:LO..HI` or `double:LO..HI`, both
        /// exponents inclusive.
        #[arg(required = true, value_name = "PROGRAM")]
        programs: Vec<ProgramSpec>,
    },
    /// Lay out the sources under each path at a page width, writing each
    /// source whose layout changes back over it.
    ///
    /// Prints the path of each source whose layout changed. Exits 0 when every
    /// source was laid out, and 2 when a path cannot be read or written, names
    /// no source, or holds a source the formatter refuses.
    Fmt
    {
        /// Write nothing; print the path of each source out of layout, and
        /// exit 1 when there is one.
        #[arg(long)]
        check: bool,
        /// The page width, in columns. Defaults to 100.
        #[arg(long, value_name = "COLUMNS")]
        width: Option<u32>,
        /// The threads the sources are laid out on.
        #[command(flatten)]
        jobs: Jobs,
        /// Source files, and directories searched for `.gandr` sources.
        #[arg(required = true)]
        paths: Vec<PathBuf>,
    },
}

/// The threads `check`, `test`, `stage` and `fmt` work on.
#[derive(Debug, clap::Args)]
#[repr(transparent)]
struct Jobs
{
    /// Work on this many threads; 1 runs everything on one. Defaults to the
    /// host's physical performance cores. The output is the same at every
    /// count.
    #[arg(long, short = 'j', env = "GANDR_JOBS", value_name = "THREADS")]
    jobs: Option<NonZeroUsize>,
}

impl From<Jobs> for Width
{
    /// The width `jobs` asks for: its count, or the host's physical
    /// performance cores when none was given.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(jobs: Jobs) -> Self
    {
        jobs.jobs.map_or(Self::PerformanceCores, |threads| {
            Self::Threads(Threads::from(threads))
        })
    }
}

/// How much of each report `check` and `test` print.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, clap::ValueEnum)]
enum Level
{
    /// The message, the labels, the nested reasons and the note.
    #[default]
    User,
    /// Adds the class, the producer's wording and the offending source text.
    Detailed,
    /// Adds byte spans and the producer's refusal as its implementers print
    /// it.
    Debug,
    /// Every report, ledger line and the run's summary as one line of JSON.
    Json,
}

impl From<Level> for Verbosity
{
    /// The verbosity `level` names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(level: Level) -> Self
    {
        match level {
            | Level::User => Self::User,
            | Level::Detailed => Self::Detailed,
            | Level::Debug => Self::Debug,
            | Level::Json => Self::Json,
        }
    }
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
///   `run` runs its script as [`script`] states, and `fmt` lays out its paths
///   as [`fmt`] states. `lsp` serves and `lsp --capabilities` prints as [`lsp`]
///   and [`capabilities`] state, `repl` runs as [`repl`] states, and `tui` as
///   [`tui`] states. Output the driver cannot write is noted on standard error,
///   when that is writable, and exits `2`.
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
/// - witness: `cli::cli::fmt_rewrites_what_check_reports`
#[spec(ensures: |ret| ret == ExitCode::SUCCESS || ret == ExitCode::from(UNSETTLED) || ret == ExitCode::from(FAULTED))]
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
    let (invocation, verbosity) = match cli.command {
        | None => (Invocation::Status, Verbosity::User),
        | Some(Command::Check {
            goals,
            verbosity,
            jobs,
            paths,
        }) => (
            Invocation::Check {
                goals: if goals { Goals::Reported } else { Goals::Gated },
                paths,
                width: Width::from(jobs),
            },
            Verbosity::from(verbosity),
        ),
        | Some(Command::Test {
            verbosity,
            jobs,
            paths,
        }) => (
            Invocation::Test {
                paths,
                width: Width::from(jobs),
            },
            Verbosity::from(verbosity),
        ),
        | Some(Command::Run { path }) => (Invocation::Run { path }, Verbosity::User),
        | Some(Command::Stage { jobs, programs }) => (
            Invocation::Stage {
                programs,
                width: Width::from(jobs),
            },
            Verbosity::User,
        ),
        | Some(Command::Fmt {
            check,
            width,
            jobs,
            paths,
        }) => (
            Invocation::Format {
                paths,
                options: width.map_or_else(FormatOptions::default, |columns| FormatOptions {
                    page: PageWidth::from(columns),
                }),
                rewrite: if check {
                    Rewrite::Check
                }
                else {
                    Rewrite::InPlace
                },
                width: Width::from(jobs),
            },
            Verbosity::User,
        ),
        | Some(Command::Lsp {
            capabilities: true, ..
        }) => return capabilities(),
        #[cfg(unix)]
        | Some(Command::Lsp {
            standalone: false,
            socket,
            linger_ms,
            ..
        }) => {
            return relayed(
                socket,
                linger_ms.map_or(gandr_surface_lsp::LINGER, Duration::from_millis),
            );
        },
        | Some(Command::Lsp { .. }) => return lsp(),
        #[cfg(unix)]
        | Some(Command::Serve { socket, linger_ms }) => {
            return hub(
                socket,
                linger_ms.map_or(gandr_surface_lsp::LINGER, Duration::from_millis),
            );
        },
        #[cfg(unix)]
        | Some(Command::Mcp { socket, linger_ms }) => {
            return mcp(
                socket,
                linger_ms.map_or(gandr_surface_lsp::LINGER, Duration::from_millis),
            );
        },
        | Some(Command::Repl { batch }) => {
            return repl(if batch { Face::Batch } else { Face::ByInput });
        },
        #[cfg(unix)]
        | Some(Command::View { socket, linger_ms }) => {
            return view(
                socket,
                linger_ms.map_or(gandr_surface_lsp::LINGER, Duration::from_millis),
            );
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
        verbosity,
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
///   not acquire request replies; each synchronisation's timing line goes to
///   standard error. The session ends as [`ended`] states.
/// - provides: the editor's entry point without a hub.
/// - fails: never by panic; every failure is an exit code.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L2/L3 — initialize/shutdown/exit, premature EOF and a
///   truncated frame are observed as protocol output and exit codes. Wrong
///   framing, lost replies and collapsed clean/abrupt/fault statuses change
///   these traces. Arbitrary methods and live-editor timing are excluded.
/// - witness: `cli::cli::lsp_serves_a_session_over_the_standard_streams`
#[spec(ensures: |ret| ret == ExitCode::SUCCESS || ret == ExitCode::from(ABRUPT) || ret == ExitCode::from(FAULTED))]
fn lsp() -> ExitCode
{
    let mut input = std::io::stdin().lock();
    let mut output = std::io::stdout().lock();
    let mut log = std::io::stderr();
    ended(gandr_surface_lsp::serve(&mut input, &mut output, &mut log))
}

/// The exit code a language-server session that ended as `served` owes.
///
/// # Specification
/// - requires: nothing.
/// - ensures: `0` after shutdown, `1` before it; a failed stream is noted on
///   standard error when writable and exits `2`.
/// - provides: one mapping for the standalone server and the relay.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — clean, abrupt and broken sessions, standalone and
///   relayed, exit with distinct codes.
/// - witness: `cli::cli::lsp_serves_a_session_over_the_standard_streams`
/// - witness: `cli::cli::lsp_clients_share_one_engine_hub`
#[spec(ensures: |ret| ret == ExitCode::SUCCESS || ret == ExitCode::from(ABRUPT) || ret == ExitCode::from(FAULTED))]
fn ended(served: Result<Served, gandr_surface_lsp::TransportFault>) -> ExitCode
{
    match served {
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

/// The socket `socket` names, or the one the current directory's workspace
/// names when it names none.
///
/// # Specification
/// trivial.
#[cfg(unix)]
fn hub_socket(socket: Option<PathBuf>) -> std::io::Result<PathBuf>
{
    match socket {
        | Some(socket) => Ok(socket),
        | None => gandr_surface_lsp::socket_for(&std::env::current_dir()?),
    }
}

/// Note `error`, what stopped reaching or running the hub, on standard error
/// when writable, and exit `2`.
///
/// # Specification
/// trivial.
#[cfg(unix)]
fn hub_fault(error: &std::io::Error) -> ExitCode
{
    match writeln!(std::io::stderr(), "gandr: the engine hub: {error}") {
        // When standard error is unwritable too, the exit code is the one
        // channel left.
        | Ok(()) | Err(_) => ExitCode::from(FAULTED),
    }
}

/// Carry the language-server session on the standard streams to the hub at
/// `socket`, starting one lingering `linger` when none answers, and choose
/// the exit code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the session runs against the hub [`reach_hub`] reaches as
///   `gandr_surface_lsp::relay` carries it, and ends as [`ended`] states; a hub
///   never reached is noted on standard error and exits `2`.
/// - provides: the editor's entry point on Unix.
/// - fails: never by panic; every failure is an exit code.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a client finding no hub starts one that outlives it by
///   its linger; two clients of one hub both end cleanly.
/// - witness: `cli::cli::lsp_clients_share_one_engine_hub`
#[cfg(unix)]
#[spec(ensures: |ret| ret == ExitCode::SUCCESS || ret == ExitCode::from(ABRUPT) || ret == ExitCode::from(FAULTED))]
fn relayed(
    socket: Option<PathBuf>,
    linger: Duration,
) -> ExitCode
{
    match reach_hub(socket, linger) {
        | Ok(stream) => ended(gandr_surface_lsp::relay(
            std::io::stdin(),
            &mut std::io::stdout().lock(),
            stream,
        )),
        | Err(error) => hub_fault(&error),
    }
}

/// Carry the Model Context Protocol session on the standard streams to the
/// hub at `socket`, starting one lingering `linger` when none answers, and
/// choose the exit code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the session runs against the hub [`reach_hub`] reaches as
///   `gandr_surface_mcp::relay` carries it and exits `0` once the hub has
///   answered all of standard input; a hub never reached or a failed stream is
///   noted on standard error and exits `2`.
/// - provides: `gandr mcp`, a model's entry point.
/// - fails: never by panic; every failure is an exit code.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a model session reads the diagnostics an editor's session
///   published through the same hub.
/// - witness: `cli::cli::mcp_reads_what_an_editor_holds_open`
#[cfg(unix)]
#[spec(ensures: |ret| ret == ExitCode::SUCCESS || ret == ExitCode::from(FAULTED))]
fn mcp(
    socket: Option<PathBuf>,
    linger: Duration,
) -> ExitCode
{
    let carried = reach_hub(socket, linger).and_then(|stream| {
        gandr_surface_mcp::relay(std::io::stdin(), &mut std::io::stdout().lock(), stream)
    });
    match carried {
        | Ok(()) => ExitCode::SUCCESS,
        | Err(error) => hub_fault(&error),
    }
}

/// Attach to the render bus of the hub at `socket`, starting one lingering
/// `linger` when none answers, follow it, and choose the exit code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the attach is sent to the hub [`reach_hub`] reaches; with
///   standard input and output both terminals, the bus is followed as
///   `gandr_surface_tui::follow` states, and otherwise its reports are printed
///   as `gandr_surface_tui::follow_plain` states. The view exits `0` when it
///   completes, and `2` when a hub is never reached, a stream fails or the view
///   ends faulted, the cause noted on standard error when writable.
/// - provides: `gandr view`, the side view beside an editor.
/// - fails: never by panic; every failure is an exit code.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a piped view prints the report of a document an editor
///   opens through the same hub, then the next one after the editor's edit.
/// - witness: `cli::cli::a_view_follows_what_an_editor_holds_open`
#[cfg(unix)]
#[spec(ensures: |ret| ret == ExitCode::SUCCESS || ret == ExitCode::from(FAULTED))]
fn view(
    socket: Option<PathBuf>,
    linger: Duration,
) -> ExitCode
{
    let attached = reach_hub(socket, linger).and_then(|mut stream| {
        stream.write_all(gandr_surface_lsp::RENDER_BUS_PREFACE.as_bytes())?;
        let reading = std::io::BufReader::new(stream.try_clone()?);
        Ok((stream, reading))
    });
    let (mut writing, reading) = match attached {
        | Ok(ends) => ends,
        | Err(error) => return hub_fault(&error),
    };
    let terminal = std::io::stdin().is_terminal() && std::io::stdout().is_terminal();
    let followed = if terminal {
        gandr_surface_tui::follow(reading, &mut writing)
    }
    else {
        gandr_surface_tui::follow_plain(reading, &mut std::io::stdout().lock())
    };
    let noted = match followed {
        | Ok(Ended::Completed) => return ExitCode::SUCCESS,
        | Ok(Ended::Faulted(fault)) => writeln!(std::io::stderr(), "gandr: the view: {fault}"),
        | Err(error) => writeln!(std::io::stderr(), "gandr: the view: {error}"),
    };
    match noted {
        // When standard error is unwritable too, the exit code is the one
        // channel left.
        | Ok(()) | Err(_) => ExitCode::from(FAULTED),
    }
}

/// A connection to the hub at `socket`, started lingering `linger` when none
/// answers.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a hub answering at once is connected; otherwise this executable
///   is started detached as `gandr serve` on the socket, and the socket is
///   tried every 20 ms for five seconds.
/// - provides: one way every client reaches its workspace's hub.
/// - fails: when the socket cannot be named, the hub cannot be started, or it
///   never answers within five seconds.
/// - panics: none.
/// - executable: none — the result is a socket connection to another process.
///
/// # Errors
/// The error naming the socket, starting the hub or connecting last.
///
/// # Adequacy
/// - hypothesis: L3 — a client finding no hub starts one, and the next client
///   connects to it.
/// - witness: `cli::cli::lsp_clients_share_one_engine_hub`
/// - witness: `cli::cli::mcp_reads_what_an_editor_holds_open`
/// - witness: `cli::cli::a_view_follows_what_an_editor_holds_open`
#[cfg(unix)]
fn reach_hub(
    socket: Option<PathBuf>,
    linger: Duration,
) -> std::io::Result<std::os::unix::net::UnixStream>
{
    use std::os::unix::net::UnixStream;
    use std::os::unix::process::CommandExt as _;

    let socket = hub_socket(socket)?;
    if let Ok(stream) = UnixStream::connect(&socket) {
        return Ok(stream);
    }
    let child = std::process::Command::new(std::env::current_exe()?)
        .arg("serve")
        .arg("--socket")
        .arg(&socket)
        .arg("--linger-ms")
        .arg(linger.as_millis().to_string())
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .process_group(0_i32)
        .spawn()?;
    // The hub outlives this client by its linger; it is never waited on.
    drop(child);
    let started = Instant::now();
    loop {
        std::thread::sleep(Duration::from_millis(20));
        match UnixStream::connect(&socket) {
            | Ok(stream) => return Ok(stream),
            | Err(error) if started.elapsed() >= Duration::from_secs(5) => return Err(error),
            | Err(_) => {},
        }
    }
}

/// Run the engine hub on `socket`, lingering `linger` once its last client
/// leaves, and choose the exit code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the hub runs as `gandr_surface_lsp::run_hub` states, with this
///   crate's Model Context Protocol face (`gandr_surface_mcp::serve`), its
///   timing lines on standard error, and exits `0` when it lingers out; a
///   socket another hub serves exits `0` at once, noted on standard error. A
///   socket that cannot be bound or served is noted and exits `2`.
/// - provides: `gandr serve`.
/// - fails: never by panic; every failure is an exit code.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a hub serving a client exits `0` after its linger and
///   removes its socket.
/// - witness: `cli::cli::lsp_clients_share_one_engine_hub`
#[cfg(unix)]
#[spec(ensures: |ret| ret == ExitCode::SUCCESS || ret == ExitCode::from(FAULTED))]
fn hub(
    socket: Option<PathBuf>,
    linger: Duration,
) -> ExitCode
{
    let socket = match hub_socket(socket) {
        | Ok(socket) => socket,
        | Err(error) => return hub_fault(&error),
    };
    match gandr_surface_lsp::bind(&socket) {
        | Ok(Maybe::Present(listener)) => {
            match gandr_surface_lsp::run_hub(
                &listener,
                &socket,
                linger,
                std::io::stderr(),
                Some(gandr_surface_mcp::serve),
            ) {
                | Ok(()) => ExitCode::SUCCESS,
                | Err(error) => hub_fault(&error),
            }
        },
        | Ok(Maybe::Absent(gandr_surface_lsp::bind::Absent::Served)) => {
            match writeln!(
                std::io::stderr(),
                "gandr: a hub already serves {}",
                socket.display()
            ) {
                | Ok(()) | Err(_) => ExitCode::SUCCESS,
            }
        },
        | Err(error) => hub_fault(&error),
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
#[spec(ensures: |ret| ret == ExitCode::SUCCESS || ret == ExitCode::from(FAULTED))]
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
#[spec(ensures: |ret| ret == ExitCode::SUCCESS || ret == ExitCode::from(FAULTED))]
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
#[spec(ensures: |ret| ret == ExitCode::SUCCESS || ret == ExitCode::from(FAULTED))]
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
#[spec(ensures: |ret| ret == ExitCode::from(FAULTED)
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
///   its diagnostics to standard error and its run status chooses the exit. A
///   staging follows [`stage`], and a formatting [`fmt`].
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
/// - witness: `cli::cli::every_width_stages_the_serial_run`
/// - witness: `cli::cli::fmt_rewrites_what_check_reports`
#[spec(captures: [status = matches!(outcome, Outcome::Status(_))],
    ensures: |ref ret| ret.as_ref().map_or(true, |exit|
        (*exit == ExitCode::SUCCESS || *exit == ExitCode::from(UNSETTLED) || *exit == ExitCode::from(FAULTED))
            && (!status || *exit == ExitCode::SUCCESS)))]
fn render(
    outcome: Outcome,
    verbosity: Verbosity,
    stdout: &mut dyn std::io::Write,
    stderr: &mut dyn std::io::Write,
) -> std::io::Result<ExitCode>
{
    match outcome {
        | Outcome::Status(report) => {
            writeln!(stdout, "gandr {} — {report}", env!("CARGO_PKG_VERSION"))?;
            Ok(ExitCode::SUCCESS)
        },
        | Outcome::Run { verb, walk, width } => run(verb, walk, width, verbosity, stdout, stderr),
        | Outcome::Script(mut runnable) => script(&mut runnable, stdout, stderr),
        | Outcome::Stage(staging) => stage(staging, stdout, stderr),
        | Outcome::Format(formatting) => fmt(formatting, stdout, stderr),
    }
}

/// Lay out `formatting`'s sources, printing the path of each whose layout
/// changed, and choose the exit code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each source whose layout changed is its path, as one line on
///   standard output, in walk order: written back under `fmt`, untouched under
///   `fmt --check`. A source already in layout prints nothing. Each path that
///   cannot be read or written back, names no source, or holds a source the
///   formatter refuses is `gandr: <path>: <fault>` on standard error, and the
///   formatting continues past it. The exit is two when any path faulted;
///   otherwise one under `fmt --check` when any source is out of layout, and
///   zero. Every byte written, every source rewritten and the exit are the same
///   at every width.
/// - provides: `gandr fmt` and `gandr fmt --check`.
/// - fails: the first write error on either stream, printing nothing after it;
///   at one thread no source after it is laid out, and at a wider one every
///   source already has been.
/// - panics: none.
///
/// # Errors
/// The [`std::io::Error`] of the first write that failed.
///
/// # Adequacy
/// - hypothesis: L3 — a source out of layout, one in layout and a missing path
///   under `fmt --check`, then `fmt`, then `fmt --check` again, observe each
///   stream, each exit, and the source's bytes after each run. Fault precedence
///   over a change, the check writing nothing and a second check passing are
///   each distinguished. Formatter refusals and unwritable sources are outside
///   these fixtures.
/// - witness: `cli::cli::fmt_rewrites_what_check_reports`
#[spec(captures: [checking = formatting.rewrite() == Rewrite::Check],
    ensures: |ref ret| ret.as_ref().map_or(true, |exit|
        *exit == ExitCode::SUCCESS || *exit == ExitCode::from(FAULTED)
            || (checking && *exit == ExitCode::from(UNFORMATTED))))]
fn fmt(
    formatting: Formatting,
    stdout: &mut dyn std::io::Write,
    stderr: &mut dyn std::io::Write,
) -> std::io::Result<ExitCode>
{
    let rewrite = formatting.rewrite();
    let (mut changed, mut faulted) = (false, false);
    let visited = formatting.visit(|step| {
        let written = match step {
            | FormatStep::Unchanged { .. } => Ok(()),
            | FormatStep::Changed { path } => {
                changed = true;
                writeln!(stdout, "{}", path.display())
            },
            | FormatStep::Fault { path, fault } => {
                faulted = true;
                writeln!(stderr, "gandr: {}: {fault}", path.display())
            },
        };
        match written {
            | Ok(()) => ControlFlow::Continue(()),
            | Err(error) => ControlFlow::Break(error),
        }
    });
    if let ControlFlow::Break(error) = visited {
        return Err(error);
    }
    Ok(match (faulted, changed, rewrite) {
        | (true, ..) => ExitCode::from(FAULTED),
        | (false, true, Rewrite::Check) => ExitCode::from(UNFORMATTED),
        | (false, false, _) | (false, true, Rewrite::InPlace) => ExitCode::SUCCESS,
    })
}

/// Check `staging`'s programs, printing one line per program, then the run's
/// digest and verdict, and choose the exit code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each program's line in order on standard output — its spelling,
///   the certificates the kernel readmitted and each family class's count, or
///   the fault that left it unchecked — then `digest: ` and sixteen hexadecimal
///   digits, then `verdict: ` and the verdict. The exit is zero when every
///   certificate was readmitted, one when the kernel refused one, and two when
///   a program could not be checked or a family's admission faulted. A pool
///   that does not start is `gandr: ` and the fault on standard error, and
///   exits two. Every byte written and the exit are the same at every width.
/// - provides: `gandr stage`.
/// - fails: the first write error on either stream.
/// - panics: none.
///
/// # Errors
/// The [`std::io::Error`] of the first write that failed.
///
/// # Adequacy
/// - hypothesis: L2/L3 — the power and double programs print the same lines,
///   digest, verdict and exit at one thread, several and the host's width, by
///   flag and by environment; a malformed spelling exits two before anything
///   runs. A refused certificate cannot be built from a spelling; its exit is
///   the dispatcher's verdict witness.
/// - witness: `cli::cli::every_width_stages_the_serial_run`
/// - witness: `cli::cli::a_malformed_invocation_exits_two`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |exit|
    *exit == ExitCode::SUCCESS || *exit == ExitCode::from(REFUSED) || *exit == ExitCode::from(FAULTED)))]
fn stage(
    staging: Staging,
    stdout: &mut dyn std::io::Write,
    stderr: &mut dyn std::io::Write,
) -> std::io::Result<ExitCode>
{
    let run = match staging.run() {
        | Ok(run) => run,
        | Err(fault) => {
            writeln!(stderr, "gandr: {fault}")?;
            return Ok(ExitCode::from(FAULTED));
        },
    };
    for staged in run.programs() {
        writeln!(stdout, "{staged}")?;
    }
    let verdict = run.verdict();
    writeln!(stdout, "digest: {}", run.digest())?;
    writeln!(stdout, "verdict: {verdict}")?;
    Ok(match verdict {
        | StageVerdict::Readmitted => ExitCode::SUCCESS,
        | StageVerdict::Refused => ExitCode::from(REFUSED),
        | StageVerdict::Faulted => ExitCode::from(FAULTED),
    })
}

/// Visit `walk` at `width` under `verb`, printing each step at `verbosity`,
/// then the report and the verdict.
///
/// # Specification
/// - requires: nothing.
/// - ensures: consumes the walk, writing each step in walk order: each entry
///   `gandr-surface-diagnostics` renders of a source step under `verb` to
///   standard output at `verbosity` — below the JSON level a report as a plain
///   snippet followed by an empty line and a ledger line as itself, at it each
///   entry as one line of JSON — and each fault as one `gandr: <path>: <fault>`
///   line to standard error; then the final report and verdict, at the JSON
///   level as one object whose `level` is `summary`. The exit is zero for
///   settled, one for unsettled and two for faulted, as the walk's final report
///   decides under the offered verb, at every verbosity. Every byte written and
///   the exit are the same at every width.
/// - provides: ordered rendering and severity aggregation for check and test.
/// - fails: the first write error, without visiting or writing anything after
///   it.
/// - panics: none.
///
/// # Errors
/// The [`std::io::Error`] of the first write that failed.
///
/// # Adequacy
/// - hypothesis: L2/L3 — mixed settled, refused and unreadable paths and
///   fixture/pending roots expose continuation, stream separation and fault
///   precedence. Missing sources, reordered severity or wrong ledger selection
///   changes exact counts and statuses. The corpus and a faulting path list
///   print byte-identical streams and exits at one thread and several, set by
///   flag and by environment. Arbitrary filesystems are excluded.
/// - witness: `cli::cli::an_unreadable_path_exits_two`
/// - witness: `cli::cli::the_test_verb_prints_every_fixture_and_pending_source`
/// - witness: `cli::cli::a_failed_diagnostic_stream_stops_later_output`
/// - witness: `cli::cli::every_width_prints_the_serial_run`
/// - witness: `cli::cli::verbosity_chooses_how_much_of_a_report_prints`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |exit|
    *exit == ExitCode::SUCCESS || *exit == ExitCode::from(UNSETTLED) || *exit == ExitCode::from(FAULTED)))]
fn run(
    verb: Verb,
    walk: Walk,
    width: Width,
    verbosity: Verbosity,
    stdout: &mut dyn std::io::Write,
    stderr: &mut dyn std::io::Write,
) -> std::io::Result<ExitCode>
{
    let visited = walk.visit(width, |step| {
        match step {
            | Step::Source { .. } => {
                for entry in entries(&step, verb) {
                    let separator = match (entry, verbosity) {
                        | (
                            Entry::Report(_),
                            Verbosity::User | Verbosity::Detailed | Verbosity::Debug,
                        ) => "\n",
                        | (Entry::Report(_), Verbosity::Json) | (Entry::Line(_), _) => "",
                    };
                    let written = writeln!(
                        stdout,
                        "{}{separator}",
                        entry.render(RenderStyle::Plain, verbosity)
                    );
                    if let Err(error) = written {
                        return ControlFlow::Break(error);
                    }
                }
            },
            | Step::Fault { path, fault } => {
                if let Err(error) = writeln!(stderr, "gandr: {}: {fault}", path.display()) {
                    return ControlFlow::Break(error);
                }
            },
        }
        ControlFlow::Continue(())
    });
    let report = match visited {
        | ControlFlow::Continue(report) => report,
        | ControlFlow::Break(error) => return Err(error),
    };
    let verdict = report.verdict(verb);
    if verbosity == Verbosity::Json {
        let summary = serde_json::json!({
            "level": "summary",
            "report": report.to_string(),
            "verdict": verdict.to_string(),
        });
        writeln!(stdout, "{summary}")?;
    }
    else {
        writeln!(stdout, "{report}")?;
        writeln!(stdout, "verdict: {verdict}")?;
    }
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
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |exit|
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
                        writeln!(
                            stderr,
                            "{}\n",
                            report.render(RenderStyle::Plain, Verbosity::User)
                        )?;
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
