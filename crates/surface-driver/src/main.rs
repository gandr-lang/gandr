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
//! | `0` | every declaration settled, a script's run returned a value, every staged certificate was readmitted, every source was laid out, a ledger was written, every exemplar held, or a census read every path; also `--help`, `--version`, a bare `gandr`, `gandr lsp --capabilities`, a language-server session ended by `exit` after `shutdown`, a Model Context Protocol session whose input ended, an engine hub that lingered out or found another serving its socket, a read-evaluate loop that reached the end of its input or `:quit`, a terminal face the user left, and `gandr tui --smoke` |
//! | `1` | at least one declaration is unsettled, or a source was not read as its root expects; a package's library states no manifest, or its `gandr.toml` was edited by hand; a script's run was blamed on a goal or stopped short of a value; the kernel refused a staged certificate; `gandr fmt --check` found a source out of layout; `gandr ledger exemplars` found an exemplar that does not hold; also a language-server session ended by `exit`, or by its input closing, before `shutdown` |
//! | `2` | an engine fault, an unreadable path or one naming no source, a malformed invocation, `check`, `test` or `fmt` given no path outside every package, a user configuration file that cannot be read or names a spelling there is none of, output the driver could not write, a package manifest that could not be read or written, a language-server or Model Context Protocol stream that failed, an engine hub that could not be reached, bound or served, a fault that stopped a read-evaluate loop or a terminal face, a terminal that failed, `gandr tui` without a terminal, a script that never reached the machine: unreadable, refused, declaring no name, or running into a declaration the machine carries no image of, or a staged program that could not be checked, a family admission that faulted, or a worker pool that did not start, or a source the formatter refused or could not write back, or a ledger that could not be generated, written or listed, or a source a census could not parse or lower, or that the lowering refused whole |
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
//! | `gandr check --grant <operations> <paths>` | as `check`, every capability a declaration holds bounded by the host operations named, comma-separated and repeatable (`--grant read,write`): one claiming another is refused by name; without the flag every held capability is owed | as `check`, and an operation no host interface offers |
//! | `gandr check --entry <worlds> <paths>` | as `check`, every declaration entered at the worlds named, comma-separated as an `entry` attribute names them (`--entry operator,seat`): its home first, then one capability per later world; a declaration stating its own entry is checked within it, and a source declaring one of the worlds nowhere grants nothing; without the flag a declaration stands where it states | as `check` |
//! | `gandr check --jobs <threads> <paths>` | as `check`, its sources parsed and lowered on that many threads | as `check` |
//! | `gandr check --lint explicit-exits <paths>` | as `check`, plus a warning for every exit the lowering inferred where a body ends, each with the fix that writes its keyword; without the flag only the declarations and modules marked `@[ explicit_exits ]` are linted | as `check`: a finding settles nothing |
//! | `gandr check --lint explicit-runs <paths>` | as `check`, plus a warning for every run the checker inferred where a computation stands in a position that reads a value, each with the fix that writes `run`; `--lint explicit-runs=effects` reports only the runs that perform an effect; without a flag only the declarations and modules marked `@[ explicit_runs ]` or `@[ explicit_runs("effects") ]` are linted | as `check`: a finding settles nothing |
//! | `gandr check --verbosity <level> <paths>` | as `check`, each report at `user` (the default), `detailed` (adding its class, the producer's wording and the offending source text), `debug` (adding byte spans and the producer's refusal) or `json` (each report, ledger line and the run's summary as one line of JSON); `test` takes the flag too | as `check` |
//! | `gandr test <paths>` | as `check`, plus every fixture, settled or not, and every pending source's refusal | as `check` |
//! | `gandr run <file>` | the value, alone, on standard output; every report `check --goals` would print, and why a run stopped or never started, on standard error | a run blamed or stuck, or a source that never reached the machine |
//! | `gandr stage <programs>` | a line per program — the certificates the kernel readmitted and its families by how they were admitted — then the run's digest and verdict | a certificate the kernel refused, a program that could not be checked, or a family admission that faulted |
//! | `gandr stage --jobs <threads> <programs>` | as `stage`, each program's stages forked onto that many threads | as `stage` |
//! | `gandr fmt <paths>` | the path of each source whose layout changed, written back over it | a path that cannot be read or written back, names no source, or holds a source the formatter refuses |
//! | `gandr fmt --check <paths>` | the path of each source out of layout; nothing is written | as `fmt`, and any source out of layout |
//! | `gandr fmt --width <columns> <paths>` | as `fmt`, laid out at that page width instead of 100 | as `fmt` |
//! | `gandr fmt --form <explicit\|sugared> <paths>` | as `fmt`, asking for that spelling: a source declaring a form with `@[ form(…) ]` keeps its own, and one declaring none is refused, since no layout changes a token | as `fmt` |
//! | `gandr fmt --jobs <threads> <paths>` | as `fmt`, its sources laid out on that many threads | as `fmt` |
//! | `gandr cells <paths>` | one line per rewriting cell of each declaration a source writes, `<path>:<line>:<column>: cell <n> <provenance>, <growth>: <hole> <count>, …`, each hole with how many times the cell's right-hand side writes it (`gandr-surface-dispatcher`'s `cells` module); nothing is checked | a path that cannot be read or names no source, or a source that does not parse or lower, or that the lowering refuses whole |
//! | `gandr ledger syntax --write <directory> [--exemplars <directory>]` | the path of each file written, `syntax.md` then `syntax.json`, each committed rule's admission read off its exemplar (`gandr-surface-dispatcher`'s `ledger` module) | a ledger that cannot be generated or written, or a committed rule whose exemplar cannot be read |
//! | `gandr ledger exemplars <directory>` | each exemplar that does not hold, `<path>: <fault>`, then the count verified and found (`gandr-surface-dispatcher`'s `ledger::exemplars` module) | an exemplar that does not hold, or a directory that cannot be listed |
//! | `gandr ledger recovery <directory>` | the near-miss table, one line per literal tile the syntax exemplars write, then each mutant whose first error marks other bytes than its mutation, `<path>:<byte>: <tile> <mutation>: <error> at <span>, not at <site>`, then the count swept (`gandr-surface-dispatcher`'s `ledger::recovery` module) | a mutant marked elsewhere, or a directory that cannot be listed |
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
//! | `gandr --spelling <unicode\|ascii> <verb>` | as the verb, every construct with a glyph (`≃`, `≅`, `⇝`, `∷`) written in that spelling: types in reports, hovers and published diagnostics, the loop's transcript; without the flag, the spelling the user's configuration file names (the `config` module), else Unicode | as the verb |
//!
//! A path is a source file of any name, or a directory searched for `.gandr`
//! sources. The directories a source sits in decide its root — `strict`,
//! `fixture`, or `fixture/pending` — and a source under none is strict
//! (`gandr-surface-dispatcher`'s `root` module). A path inside a package — the
//! sources beside a `lib.gandr`, rooted above it when it sits in `src` — stands
//! for the whole package, and `check`, `test` and `fmt` given no path work on
//! the package the working directory sits in, or, in no package, on every
//! member a `workspace.gandr` above it names, as they do given the workspace's
//! directory (`gandr-surface-dispatcher`'s `package` and `workspace` modules).
//! After its walk, `check` reconciles each such package's
//! `gandr.toml` with the library's `Package` model, `manifest: <path>:
//! written`, `rewritten` or `unchanged` on standard output; a manifest edited
//! by hand is left as it stands and is `gandr: <path>: drifted: …` on standard
//! error. A refusal, an unsettled
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
//! it runs the `main` it declares at its top level
//! (`gandr-surface-dispatcher`'s `script` module), each line it prints written
//! to standard output as it runs, and exits with the status `main` returns or
//! passes to `Proc.exit`. A run blamed on a goal, stuck or unfinished is
//! `` gandr: <path>: `main` <what it came to> `` on standard error; a source
//! carrying a refusal is `gandr: <path>: refused; nothing ran` after its
//! reports, and one declaring no `main` runs nothing — not its last
//! declaration — and is one line on standard error naming `def main` and
//! pointing at `gandr check` and `gandr test`.
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
//! # References
//!
//! - `vault:01a178aa-6e2c-7720-a0bd-c5e1f9c4e08e` — background: § quant-counts
//!   and § quant-try-first — a hole's occurrence count under a cell's step is
//!   reported per cell by `gandr cells`, never refused.
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
//! `tests::cli::a_script_that_runs_its_main_leaves_successfully` (exit `0`,
//! the line its `main` prints alone on standard output),
//! `tests::cli::a_script_that_blames_leaves_with_a_failure_status` (exit `1`)
//! and `tests::cli::an_ill_typed_script_is_refused_by_the_checker` (exit `2`);
//! `tests::cli::a_script_with_no_program_is_refused` asserts a source declaring
//! no `main` runs nothing.
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
//! fault’s `gandr:` line on stderr; stdout and exit codes are unchanged. A
//! diagnostic an unwritable stderr refuses is dropped: the subscriber's
//! internal-error report, which would `eprintln!` to that same stream and
//! panic, is off.
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

// Module documentation that predates the shape lint: 6 headings outside the
// vocabulary, 1 decision record and 2 budgets exceeded. Each allow leaves with
// the rewrite that clears its count.
#![cfg_attr(
    dylint_lib = "quenchant_dylints",
    allow(
        module_doc_heading,
        doc_decision_record,
        module_doc_budget,
        reason = "module documentation that predates the shape lint"
    )
)]
use core::num::NonZeroUsize;
use core::ops::ControlFlow;
#[cfg(unix)]
use core::time::Duration;
use std::io::IsTerminal as _;
use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::process::ExitCode;
#[cfg(unix)]
use std::time::Instant;

use anodized::spec;
use gandr_surface_diagnostics::Lint;
use gandr_surface_diagnostics::Severity;
use gandr_surface_diagnostics::Verbosity;
use gandr_surface_dispatcher::Area;
use gandr_surface_dispatcher::AuthorityError;
use gandr_surface_dispatcher::Census;
use gandr_surface_dispatcher::CensusStep;
use gandr_surface_dispatcher::Composed;
use gandr_surface_dispatcher::Console;
use gandr_surface_dispatcher::Entered;
use gandr_surface_dispatcher::Evaluation;
use gandr_surface_dispatcher::FeatureId;
use gandr_surface_dispatcher::FormatStep;
use gandr_surface_dispatcher::Formatting;
use gandr_surface_dispatcher::Goals;
use gandr_surface_dispatcher::HostGrant;
use gandr_surface_dispatcher::Invocation;
use gandr_surface_dispatcher::Kept;
use gandr_surface_dispatcher::LIBRARY;
use gandr_surface_dispatcher::LedgerRun;
use gandr_surface_dispatcher::LedgerTask;
use gandr_surface_dispatcher::Line;
use gandr_surface_dispatcher::Lints;
use gandr_surface_dispatcher::Manifest;
use gandr_surface_dispatcher::ManifestFault;
use gandr_surface_dispatcher::OperationName;
use gandr_surface_dispatcher::Outcome;
use gandr_surface_dispatcher::Package;
use gandr_surface_dispatcher::Pool;
use gandr_surface_dispatcher::Printed;
use gandr_surface_dispatcher::ProgramSpec;
use gandr_surface_dispatcher::Ran;
use gandr_surface_dispatcher::Rewrite;
use gandr_surface_dispatcher::RunStatus;
use gandr_surface_dispatcher::RunVerdict;
use gandr_surface_dispatcher::Script;
use gandr_surface_dispatcher::ScriptRun;
use gandr_surface_dispatcher::StageVerdict;
use gandr_surface_dispatcher::Staging;
use gandr_surface_dispatcher::Standing;
use gandr_surface_dispatcher::Status;
use gandr_surface_dispatcher::Step;
use gandr_surface_dispatcher::Threads;
use gandr_surface_dispatcher::Unmanifested;
use gandr_surface_dispatcher::Unpathed;
use gandr_surface_dispatcher::Verb;
use gandr_surface_dispatcher::Walk;
use gandr_surface_dispatcher::Width;
use gandr_surface_dispatcher::WorldName;
use gandr_surface_dispatcher::entries;
use gandr_surface_dispatcher::packaged;
use gandr_surface_dispatcher::reconcile;
use gandr_surface_format::Form;
use gandr_surface_format::FormatOptions;
use gandr_surface_format::PageWidth;
use gandr_surface_grammar::Spelling;
use gandr_surface_lsp::Capabilities;
use gandr_surface_lsp::Served;
use gandr_surface_render_terminal::RenderStyle;
use gandr_surface_render_terminal::TerminalCapability;
use gandr_surface_repl::Ended;
use quenchant_shape::shape::Maybe;

mod allocator;
mod config;

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

/// The exit code of `ledger exemplars` over an exemplar that does not hold.
const UNEXEMPLIFIED: u8 = 1;

/// gandr language toolchain driver.
#[derive(Debug, clap::Parser)]
#[command(name = "gandr", version, about)]
struct Cli
{
    /// Write every construct that has a glyph in this spelling, over the
    /// `presentation.spelling` of the user's configuration file.
    #[arg(long, global = true, value_enum)]
    spelling: Option<SpellingName>,
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
        /// Report every finding of the named lint, not only within the forms
        /// an attribute enables it on; repeatable.
        #[arg(long, value_enum)]
        lint: Vec<LintName>,
        /// Bound every capability a declaration holds by these host
        /// operations, comma-separated; repeatable. A held capability claiming
        /// any other is refused. Without it, every held capability is owed.
        #[arg(long, value_delimiter = ',', value_name = "OPERATIONS")]
        grant: Option<Vec<OperationName>>,
        /// Enter every declaration at these worlds, comma-separated: its home
        /// first, then the world of each capability the host hands it, as an
        /// `entry` attribute names them. A declaration stating its own entry
        /// is checked within this one. Without it, a declaration stands where
        /// it states.
        #[arg(long, value_delimiter = ',', value_name = "WORLDS")]
        entry: Vec<WorldName>,
        /// How much of each report to print.
        #[arg(long, value_enum, default_value_t = Level::User)]
        verbosity: Level,
        /// The threads the sources are parsed and lowered on.
        #[command(flatten)]
        jobs: Jobs,
        /// Source files, and directories searched for `.gandr` sources. A
        /// path inside a package checks the whole package, and writes its
        /// `gandr.toml`; a workspace's directory checks each member it names;
        /// with no path, the package the working directory sits in, or the
        /// workspace when it sits in none.
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
        /// Source files, and directories searched for `.gandr` sources. A
        /// path inside a package runs the whole package, a workspace's
        /// directory each member it names; with no path, the package the
        /// working directory sits in, or the workspace when it sits in none.
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
    /// Run a source as a program: check it as `check` does, then run the
    /// `main` it declares at its top level. A source declaring no `main` runs
    /// nothing.
    ///
    /// A `main` returns the exit code, `def main() -> -F Integer`, or the
    /// unit, `def main() -> -F [Console] Unit`, for 0, and reads the
    /// arguments after the path when it takes them, `def main(args :
    /// List(String)) -> -F Integer`; `Proc.exit(n)` ends the run with `n`, and
    /// `Console.print(s)` writes `s` as a line of standard output.
    /// Exits with that code, its low byte; otherwise 1 when the run is blamed
    /// on a goal or stops short of one, and 2 when the source never reaches
    /// the machine or declares no `main`.
    Run
    {
        /// The source file to run.
        path: PathBuf,
        /// The arguments the program's `main` reads, in order.
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        arguments: Vec<String>,
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
        /// The spelling each source is laid out in, explicit or sugared,
        /// through the formatter's named rewrites; a source's own
        /// `@[ form(…) ]` declaration wins. Defaults to each source's own
        /// spelling, every token kept.
        #[arg(long, value_enum)]
        form: Option<FormName>,
        /// The threads the sources are laid out on.
        #[command(flatten)]
        jobs: Jobs,
        /// Source files, and directories searched for `.gandr` sources. A
        /// path inside a package lays out the whole package, a workspace's
        /// directory each member it names; with no path, the package the
        /// working directory sits in, or the workspace when it sits in none.
        paths: Vec<PathBuf>,
    },
    /// Report the rewriting cells of the sources under each path, one line
    /// per cell, each hole with how many times the cell's right-hand side
    /// writes it.
    ///
    /// A hole's count is its Lipschitz constant under the step: 0 for a
    /// dropped hole, 1 for a kept one, more for a duplicated one. Nothing is
    /// checked. Exits 0 when every path was read, and 2 when a path cannot be
    /// read, names no source, or holds a source the lowering cannot read.
    Cells
    {
        /// Source files, and directories searched for `.gandr` sources.
        #[arg(required = true)]
        paths: Vec<PathBuf>,
    },
    /// Generate a ledger of the language surface and write it, verify its
    /// exemplars, or read the features ledger.
    ///
    /// Prints the path of each file written, each exemplar that does not hold
    /// and a count, or the features asked for. Exits 0 when the ledger was
    /// written, every exemplar holds or the features were read, 1 when an
    /// exemplar does not hold, and 2 when the ledger cannot be generated, read
    /// or answer, or a file cannot be written or listed.
    Ledger
    {
        /// The ledger to write, verify or read.
        #[command(subcommand)]
        ledger: LedgerName,
    },
}

/// The ledgers `gandr ledger` writes, verifies or reads.
#[derive(Debug, clap::Subcommand)]
enum LedgerName
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
        /// The feature's id, as `gandr ledger list` prints it.
        id: String,
        /// The tree holding `ledger/features.sql` and the paths it names.
        #[arg(long, value_name = "DIRECTORY", default_value = ".")]
        root: PathBuf,
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
            Level::User => Self::User,
            Level::Detailed => Self::Detailed,
            Level::Debug => Self::Debug,
            Level::Json => Self::Json,
        }
    }
}

/// A lint `check --lint` enables everywhere, beyond the forms an attribute
/// enables it on, each spelled as the lint is.
#[derive(Clone, Copy, Debug, Eq, PartialEq, clap::ValueEnum)]
enum LintName
{
    /// `explicit-exits`: every exit the lowering inferred where a path
    /// through a body ends.
    #[value(name = "explicit-exits")]
    Exits,
    /// `explicit-runs`: every run the checker inferred where a computation
    /// stands in a position that reads a value.
    #[value(name = "explicit-runs")]
    Runs,
    /// `explicit-runs` under its `effects` option: every inferred run that
    /// performs an effect.
    #[value(name = "explicit-runs=effects")]
    EffectfulRuns,
}

/// A spelling `fmt --form` asks for.
#[derive(Clone, Copy, Debug, Eq, PartialEq, clap::ValueEnum)]
enum FormName
{
    /// The core's explicit spelling.
    Explicit,
    /// The surface's sugared spelling.
    Sugared,
}

/// A status `ledger list --status` names.
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

/// A spelling `--spelling` names.
#[derive(Clone, Copy, Debug, Eq, PartialEq, clap::ValueEnum)]
enum SpellingName
{
    /// Each glyph: `≃`, `≅`, `⇝`, `∷`.
    Unicode,
    /// Each glyph's ASCII spelling: `<~>`, `Iso(A, B)`, `~~>`, `::`.
    Ascii,
}

impl From<SpellingName> for Spelling
{
    /// The spelling `name` names.
    ///
    /// # Specification
    /// trivial.
    #[inline]
    fn from(name: SpellingName) -> Self
    {
        match name {
            SpellingName::Unicode => Self::Unicode,
            SpellingName::Ascii => Self::Ascii,
        }
    }
}

/// How a verb prints what it reports: how much of each report, and the
/// spelling every type and value is written in.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Printing
{
    /// How much of each report prints.
    verbosity: Verbosity,
    /// The spelling every type and value is written in.
    spelling: Spelling,
}

/// What a walk is run as: its verb, the lints it reports, and the packages
/// whose manifests a `check` reconciles.
#[derive(Clone, Copy, Debug)]
struct Pass<'packages>
{
    /// The verb the walk runs under.
    verb: Verb,
    /// The lints reported beyond their attributes.
    lints: Lints,
    /// The packages the walk's paths reached.
    packages: &'packages [Package],
}

/// The spelling `flag` names, else the one the user's configuration file
/// names, else [`Spelling::Unicode`].
///
/// # Specification
/// - requires: nothing.
/// - ensures: a named flag wins without the file being read; otherwise the file
///   is read as `config::read` states and its spelling, or Unicode when it
///   names none, is the answer.
/// - provides: the one precedence every face's spelling follows.
/// - fails: the file's fault, when the flag names nothing.
/// - panics: none.
/// - executable: none — the result depends on the environment and the file
///   system.
///
/// # Errors
/// The [`config::Fault`] reading the file met.
///
/// # Adequacy
/// - hypothesis: L3 — a configured spelling prints, a flag outranks it, and a
///   malformed file stops the run, through the binary.
/// - witness: `tests::cli::the_configured_spelling_prints_and_the_flag_outranks_it_782`
fn spelling(flag: Option<SpellingName>) -> Result<Spelling, config::Fault>
{
    match flag {
        Some(name) => Ok(Spelling::from(name)),
        None => Ok(config::read()?.spelling.unwrap_or_default()),
    }
}

/// The lints `names` enable everywhere, each widening the reach the others
/// leave: `explicit-runs` reaches every run whether or not
/// `explicit-runs=effects` is named beside it.
///
/// # Specification
/// trivial.
fn enabled(names: &[LintName]) -> Lints
{
    let lints = Lints::enabling(names.iter().filter_map(|name| match *name {
        LintName::Exits => Some(Lint::ExplicitExits),
        LintName::Runs => Some(Lint::ExplicitRuns),
        LintName::EffectfulRuns => None,
    }));
    if names.contains(&LintName::EffectfulRuns) {
        lints.asking_effects()
    }
    else {
        lints
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
///   `0`. `check`, `test` and `fmt` first widen each path inside a package to
///   the whole package and a workspace's directory to its source and members,
///   and with no path take the package the working directory sits in, else the
///   workspace it sits in, exiting `2` with one `gandr:` line outside both or
///   for a workspace naming no packages (`gandr-surface-dispatcher`'s
///   `packaged`). `check` and `test` walk their paths, print what [`render`]
///   prints, and exit `0`, `1` or `2` as the run settled, was unsettled or
///   faulted, `check` reconciling each package's manifest as [`run`] states;
///   `run` runs its script as [`script`] states, and `fmt` lays out its paths
///   as [`fmt`] states. `lsp` serves and `lsp --capabilities` prints as [`lsp`]
///   and [`capabilities`] state, `repl` runs as [`repl`] states, and `tui` as
///   [`tui`] states. Every face writes its types and values in the spelling
///   [`spelling`] resolves; a configuration file that cannot be read is `gandr:
///   <path>: <fault>` on standard error and exits `2` before any verb runs.
///   Output the driver cannot write is noted on standard error, when that is
///   writable, and exits `2`.
/// - provides: the exit code as the run's verdict. With `tracing`, a
///   thread-local subscriber reports dispatch spans to standard error after
///   argument parsing.
/// - fails: never by panic or abort; every failure is an exit code.
/// - panics: none. Output goes through locked handles and the fallible
///   `writeln!`, never `println!`, whose write-failure path panics. Clap's
///   command-definition assertions fire only under `debug_assertions`.
/// - executable: none — `run` exits with a program's own status, any byte, so
///   the codes the other verbs keep to are observed by the witnesses.
///
/// # Adequacy
/// - hypothesis: L2/L3 — finite settled, refused, owed, missing and malformed
///   inputs exercise each process status and stream role. Closed output pipes
///   distinguish swallowed writes; protocol sessions distinguish completion
///   from abrupt termination. Misrouting, wrong severity and reordered output
///   change these observations. Arbitrary terminal environments and tracing
///   presentation are outside the subprocess domain.
/// - witness: `tests::cli::a_settled_run_exits_zero`
/// - witness: `tests::cli::an_unsettled_run_exits_one`
/// - witness: `tests::cli::an_unreadable_path_exits_two`
/// - witness: `tests::cli::a_malformed_invocation_exits_two`
/// - witness: `tests::cli::unwritable_standard_output_exits_two`
/// - witness: `tests::cli::status_and_version_identify_the_same_build`
/// - witness: `tests::cli::lsp_serves_a_session_over_the_standard_streams`
/// - witness: `tests::cli::a_piped_repl_session_prints_its_transcript`
/// - witness: `tests::cli::smoke_is_terminal_free_but_interactive_tui_refuses_pipes`
/// - witness: `tests::cli::a_script_that_runs_its_main_leaves_successfully`
/// - witness: `tests::cli::a_script_that_blames_leaves_with_a_failure_status`
/// - witness: `tests::cli::an_ill_typed_script_is_refused_by_the_checker`
/// - witness: `tests::cli::fmt_rewrites_what_check_reports`
/// - witness: `tests::cli::the_configured_spelling_prints_and_the_flag_outranks_it_782`
/// - witness: `tests::cli::a_verb_with_no_path_checks_the_package_it_runs_in_2687`
fn main() -> ExitCode
{
    let cli = match <Cli as clap::Parser>::try_parse() {
        Ok(cli) => cli,
        Err(error) => return usage(&error),
    };
    let spelling = match spelling(cli.spelling) {
        Ok(spelling) => spelling,
        Err(fault) => {
            return match writeln!(std::io::stderr(), "gandr: {fault}") {
                // When standard error is unwritable too, the exit code is the
                // one channel left.
                Ok(()) | Err(_) => ExitCode::from(FAULTED),
            };
        },
    };
    #[cfg(feature = "tracing")]
    let _subscriber = tracing::subscriber::set_default(
        tracing_subscriber::fmt()
            .with_writer(std::io::stderr)
            .with_span_events(tracing_subscriber::fmt::format::FmtSpan::CLOSE)
            // A diagnostic the stream refuses is dropped: the subscriber's own
            // report of the failure would go to the same refused stream
            // through `eprintln!`, which panics.
            .log_internal_errors(false)
            .finish(),
    );
    #[cfg(feature = "tracing")]
    let _span = tracing::info_span!("driver").entered();
    // The packages a `check` reached, whose manifests it reconciles.
    let mut packages: Vec<Package> = Vec::new();
    let (invocation, verbosity) = match cli.command {
        None => (Invocation::Status, Verbosity::User),
        Some(Command::Check {
            goals,
            lint,
            grant,
            entry,
            verbosity,
            jobs,
            paths,
        }) => {
            let grant = match grant {
                None => HostGrant::UNBOUNDED,
                Some(operations) => match HostGrant::within(&operations) {
                    Ok(grant) => grant,
                    Err(refused) => return ungranted(&refused),
                },
            };
            let grant = grant.entering(entry);
            let paths = match packaged(paths, Path::new(".")) {
                Ok((paths, reached)) => {
                    packages = reached;
                    paths
                },
                Err(unpackaged) => return unpathed(&unpackaged),
            };
            (
                Invocation::Check {
                    goals: if goals { Goals::Reported } else { Goals::Gated },
                    lints: enabled(&lint),
                    grant,
                    paths,
                    width: Width::from(jobs),
                },
                Verbosity::from(verbosity),
            )
        },
        Some(Command::Test {
            verbosity,
            jobs,
            paths,
        }) => (
            Invocation::Test {
                paths: match packaged(paths, Path::new(".")) {
                    Ok((paths, _)) => paths,
                    Err(unpackaged) => return unpathed(&unpackaged),
                },
                width: Width::from(jobs),
            },
            Verbosity::from(verbosity),
        ),
        Some(Command::Run { path, arguments }) => {
            (Invocation::Run { path, arguments }, Verbosity::User)
        },
        Some(Command::Stage { jobs, programs }) => (
            Invocation::Stage {
                programs,
                width: Width::from(jobs),
            },
            Verbosity::User,
        ),
        Some(Command::Fmt {
            check,
            width,
            form,
            jobs,
            paths,
        }) => (
            Invocation::Format {
                paths: match packaged(paths, Path::new(".")) {
                    Ok((paths, _)) => paths,
                    Err(unpackaged) => return unpathed(&unpackaged),
                },
                options: FormatOptions {
                    page: width.map_or_else(|| FormatOptions::default().page, PageWidth::from),
                    form: match form {
                        None => Form::Source,
                        Some(FormName::Explicit) => Form::Explicit,
                        Some(FormName::Sugared) => Form::Sugared,
                    },
                    ..FormatOptions::default()
                },
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
        Some(Command::Cells { paths }) => (Invocation::Cells { paths }, Verbosity::User),
        Some(Command::Ledger {
            ledger: LedgerName::Syntax { write, exemplars },
        }) => (
            Invocation::Ledger(LedgerTask::Syntax {
                exemplars: exemplars.unwrap_or_else(|| write.join("exemplars")),
                directory: write,
            }),
            Verbosity::User,
        ),
        Some(Command::Ledger {
            ledger: LedgerName::Exemplars { directory },
        }) => (
            Invocation::Ledger(LedgerTask::Exemplars { directory }),
            Verbosity::User,
        ),
        Some(Command::Ledger {
            ledger: LedgerName::Recovery { directory },
        }) => (
            Invocation::Ledger(LedgerTask::Recovery { directory }),
            Verbosity::User,
        ),
        Some(Command::Ledger {
            ledger: LedgerName::List { area, status, root },
        }) => (
            Invocation::Ledger(LedgerTask::List {
                root,
                area: area.map(Area),
                status: status.map(Status::from),
            }),
            Verbosity::User,
        ),
        Some(Command::Ledger {
            ledger: LedgerName::Show { id, root },
        }) => (
            Invocation::Ledger(LedgerTask::Show {
                root,
                id: FeatureId(id),
            }),
            Verbosity::User,
        ),
        Some(Command::Lsp {
            capabilities: true, ..
        }) => return capabilities(),
        #[cfg(unix)]
        Some(Command::Lsp {
            standalone: false,
            socket,
            linger_ms,
            ..
        }) => {
            return relayed(
                socket,
                linger_ms.map_or(gandr_surface_lsp::LINGER, Duration::from_millis),
                spelling,
            );
        },
        Some(Command::Lsp { .. }) => return lsp(spelling),
        #[cfg(unix)]
        Some(Command::Serve { socket, linger_ms }) => {
            return hub(
                socket,
                linger_ms.map_or(gandr_surface_lsp::LINGER, Duration::from_millis),
                spelling,
            );
        },
        #[cfg(unix)]
        Some(Command::Mcp { socket, linger_ms }) => {
            return mcp(
                socket,
                linger_ms.map_or(gandr_surface_lsp::LINGER, Duration::from_millis),
                spelling,
            );
        },
        Some(Command::Repl { batch }) => {
            return repl(if batch { Face::Batch } else { Face::ByInput }, spelling);
        },
        #[cfg(unix)]
        Some(Command::View { socket, linger_ms }) => {
            return view(
                socket,
                linger_ms.map_or(gandr_surface_lsp::LINGER, Duration::from_millis),
                spelling,
            );
        },
        Some(Command::Tui { smoke }) => {
            return tui(
                if smoke {
                    Screen::Smoke
                }
                else {
                    Screen::Terminal
                },
                spelling,
            );
        },
    };
    let mut stdout = std::io::stdout().lock();
    let mut stderr = std::io::stderr().lock();
    let rendered = render(
        gandr_surface_dispatcher::dispatch(invocation),
        Printing {
            verbosity,
            spelling,
        },
        &packages,
        &mut stdout,
        &mut stderr,
    );
    let flushed = rendered.and_then(|exit| stdout.flush().map(|()| exit));
    match flushed {
        Ok(exit) => {
            #[cfg(feature = "tracing")]
            tracing::info!("output flushed");
            exit
        },
        Err(error) => match writeln!(stderr, "gandr: cannot write the output: {error}") {
            // When standard error is unwritable too, the exit code is the one
            // channel left.
            Ok(()) | Err(_) => ExitCode::from(FAULTED),
        },
    }
}

/// Serve the language server over standard input and output until the
/// session ends, its user's configuration naming `spelling`, its kernel
/// admissions on a pool at the host's width, and choose the exit code.
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
/// - witness: `tests::cli::lsp_serves_a_session_over_the_standard_streams`
#[spec(ensures: |ret| ret == ExitCode::SUCCESS || ret == ExitCode::from(ABRUPT) || ret == ExitCode::from(FAULTED))]
fn lsp(spelling: Spelling) -> ExitCode
{
    let mut input = std::io::BufReader::new(std::io::stdin());
    let mut output = std::io::stdout().lock();
    let mut log = std::io::stderr();
    ended(gandr_surface_lsp::serve(
        &mut input,
        &mut output,
        &mut log,
        (workspace(spelling), &Pool::new(Width::PerformanceCores)),
    ))
}

/// The workspace a language server or a hub serves over: its user's
/// configuration naming `spelling`, and its saves kept in the directory
/// [`config::checkpoints`] names. A directory that cannot be made keeps no
/// save, noted on standard error, and the server serves on.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a workspace spelled `spelling`, keeping saves when a cache
///   directory is named and can be made.
/// - provides: one workspace for `gandr lsp` and `gandr serve`.
/// - fails: never.
/// - panics: none.
/// - executable: none — the result depends on the environment and the file
///   system, which the clauses cannot observe.
///
/// # Adequacy
/// - hypothesis: L3 — a session served over the standard streams.
/// - witness: `tests::cli::lsp_serves_a_session_over_the_standard_streams`
fn workspace(spelling: Spelling) -> gandr_surface_lsp::Workspace
{
    let workspace = gandr_surface_lsp::Workspace::spelled(spelling);
    let Some(directory) = config::checkpoints()
    else {
        return workspace;
    };
    match gandr_surface_lsp::Saved::at(&directory) {
        Ok(saved) => workspace.saving(saved),
        Err(error) => {
            let _noted = writeln!(
                std::io::stderr(),
                "gandr: {}: saves keep no checkpoints: {error}",
                directory.display()
            );
            workspace
        },
    }
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
/// - witness: `tests::cli::lsp_serves_a_session_over_the_standard_streams`
/// - witness: `tests::cli::lsp_clients_share_one_engine_hub`
#[spec(ensures: |ret| ret == ExitCode::SUCCESS || ret == ExitCode::from(ABRUPT) || ret == ExitCode::from(FAULTED))]
fn ended(served: Result<Served, gandr_surface_lsp::TransportFault>) -> ExitCode
{
    match served {
        Ok(Served::Clean) => ExitCode::SUCCESS,
        Ok(Served::Abrupt) => ExitCode::from(ABRUPT),
        Err(fault) => {
            match writeln!(
                std::io::stderr(),
                "gandr: the language server stopped: {fault}"
            ) {
                // When standard error is unwritable too, the exit code is the
                // one channel left.
                Ok(()) | Err(_) => ExitCode::from(FAULTED),
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
        Some(socket) => Ok(socket),
        None => gandr_surface_lsp::socket_for(&std::env::current_dir()?),
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
        Ok(()) | Err(_) => ExitCode::from(FAULTED),
    }
}

/// Carry the language-server session on the standard streams to the hub at
/// `socket`, starting one lingering `linger` and configured with `spelling`
/// when none answers, and choose the exit code.
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
/// - witness: `tests::cli::lsp_clients_share_one_engine_hub`
#[cfg(unix)]
#[spec(ensures: |ret| ret == ExitCode::SUCCESS || ret == ExitCode::from(ABRUPT) || ret == ExitCode::from(FAULTED))]
fn relayed(
    socket: Option<PathBuf>,
    linger: Duration,
    spelling: Spelling,
) -> ExitCode
{
    match reach_hub(socket, linger, spelling) {
        Ok(stream) => ended(gandr_surface_lsp::relay(
            std::io::stdin(),
            &mut std::io::stdout().lock(),
            stream,
        )),
        Err(error) => hub_fault(&error),
    }
}

/// Carry the Model Context Protocol session on the standard streams to the
/// hub at `socket`, starting one lingering `linger` and configured with
/// `spelling` when none answers, and choose the exit code.
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
/// - witness: `tests::cli::mcp_reads_what_an_editor_holds_open`
#[cfg(unix)]
#[spec(ensures: |ret| ret == ExitCode::SUCCESS || ret == ExitCode::from(FAULTED))]
fn mcp(
    socket: Option<PathBuf>,
    linger: Duration,
    spelling: Spelling,
) -> ExitCode
{
    let carried = reach_hub(socket, linger, spelling).and_then(|stream| {
        gandr_surface_mcp::relay(std::io::stdin(), &mut std::io::stdout().lock(), stream)
    });
    match carried {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => hub_fault(&error),
    }
}

/// Attach to the render bus of the hub at `socket`, starting one lingering
/// `linger` and configured with `spelling` when none answers, follow it, and
/// choose the exit code.
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
/// - witness: `tests::cli::a_view_follows_what_an_editor_holds_open`
#[cfg(unix)]
#[spec(ensures: |ret| ret == ExitCode::SUCCESS || ret == ExitCode::from(FAULTED))]
fn view(
    socket: Option<PathBuf>,
    linger: Duration,
    spelling: Spelling,
) -> ExitCode
{
    let attached = reach_hub(socket, linger, spelling).and_then(|mut stream| {
        stream.write_all(gandr_surface_lsp::RENDER_BUS_PREFACE.as_bytes())?;
        let reading = std::io::BufReader::new(stream.try_clone()?);
        Ok((stream, reading))
    });
    let (mut writing, reading) = match attached {
        Ok(ends) => ends,
        Err(error) => return hub_fault(&error),
    };
    let terminal = std::io::stdin().is_terminal() && std::io::stdout().is_terminal();
    let followed = if terminal {
        gandr_surface_tui::follow(reading, &mut writing)
    }
    else {
        gandr_surface_tui::follow_plain(reading, &mut std::io::stdout().lock())
    };
    let noted = match followed {
        Ok(Ended::Completed) => return ExitCode::SUCCESS,
        Ok(Ended::Faulted(fault)) => writeln!(std::io::stderr(), "gandr: the view: {fault}"),
        Err(error) => writeln!(std::io::stderr(), "gandr: the view: {error}"),
    };
    match noted {
        // When standard error is unwritable too, the exit code is the one
        // channel left.
        Ok(()) | Err(_) => ExitCode::from(FAULTED),
    }
}

/// A connection to the hub at `socket`, started lingering `linger` and
/// configured with `spelling` when none answers.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a hub answering at once is connected; otherwise this executable
///   is started detached as `gandr serve` on the socket with `--spelling`
///   naming `spelling`, and the socket is tried every 20 ms for five seconds.
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
/// - witness: `tests::cli::lsp_clients_share_one_engine_hub`
/// - witness: `tests::cli::mcp_reads_what_an_editor_holds_open`
/// - witness: `tests::cli::a_view_follows_what_an_editor_holds_open`
#[cfg(unix)]
fn reach_hub(
    socket: Option<PathBuf>,
    linger: Duration,
    spelling: Spelling,
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
        .arg("--spelling")
        .arg(match spelling {
            Spelling::Unicode => "unicode",
            Spelling::Ascii => "ascii",
        })
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
            Ok(stream) => return Ok(stream),
            Err(error) if started.elapsed() >= Duration::from_secs(5) => return Err(error),
            Err(_) => {},
        }
    }
}

/// Run the engine hub on `socket`, lingering `linger` once its last client
/// leaves, its workspace configured with `spelling`, its kernel admissions on
/// a pool at the host's width, and choose the exit code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the hub binds `socket` through `gandr_surface_lsp::bind` and runs
///   as `gandr_surface_lsp::run_hub` states, with this crate's Model Context
///   Protocol face (`gandr_surface_mcp::serve`) for connections speaking lines,
///   its timing lines on standard error, and exits `0` when it lingers out; a
///   socket another hub serves exits `0` at once, noted on standard error. A
///   socket that cannot be bound or served is noted and exits `2`.
/// - provides: `gandr serve`.
/// - fails: never by panic; every failure is an exit code.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — a hub serving a client exits `0` after its linger and
///   removes its socket.
/// - witness: `tests::cli::lsp_clients_share_one_engine_hub`
#[cfg(unix)]
#[spec(ensures: |ret| ret == ExitCode::SUCCESS || ret == ExitCode::from(FAULTED))]
fn hub(
    socket: Option<PathBuf>,
    linger: Duration,
    spelling: Spelling,
) -> ExitCode
{
    let socket = match hub_socket(socket) {
        Ok(socket) => socket,
        Err(error) => return hub_fault(&error),
    };
    match gandr_surface_lsp::bind(&socket) {
        Ok(Maybe::Present(listener)) => {
            match gandr_surface_lsp::run_hub(
                &listener,
                &socket,
                linger,
                std::io::stderr(),
                Some(gandr_surface_mcp::serve),
                (workspace(spelling), Pool::new(Width::PerformanceCores)),
            ) {
                Ok(()) => ExitCode::SUCCESS,
                Err(error) => hub_fault(&error),
            }
        },
        Ok(Maybe::Absent(gandr_surface_lsp::bind::Absent::Served)) => {
            match writeln!(
                std::io::stderr(),
                "gandr: a hub already serves {}",
                socket.display()
            ) {
                Ok(()) | Err(_) => ExitCode::SUCCESS,
            }
        },
        Err(error) => hub_fault(&error),
    }
}

/// Run the read-evaluate loop on the standard streams, writing its types and
/// values in `spelling`, and choose the exit code.
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
/// - witness: `tests::cli::a_piped_repl_session_prints_its_transcript`
#[spec(ensures: |ret| ret == ExitCode::SUCCESS || ret == ExitCode::from(FAULTED))]
fn repl(
    face: Face,
    spelling: Spelling,
) -> ExitCode
{
    let input = std::io::stdin();
    let mut output = std::io::stdout().lock();
    let ended = match (face, input.is_terminal()) {
        (Face::Batch, _) | (Face::ByInput, false) => {
            gandr_surface_repl::run_batch(input.lock(), &mut output, RenderStyle::Plain, spelling)
        },
        (Face::ByInput, true) => {
            let style = RenderStyle::for_terminal(TerminalCapability::from(output.is_terminal()));
            gandr_surface_repl::run_interactive(&mut output, style, spelling)
        },
    };
    let noted = match ended {
        Ok(Ended::Completed) => return ExitCode::SUCCESS,
        Ok(Ended::Faulted(fault)) => writeln!(std::io::stderr(), "gandr: {fault}"),
        Err(error) => writeln!(std::io::stderr(), "gandr: cannot write the output: {error}"),
    };
    match noted {
        // When standard error is unwritable too, the exit code is the one
        // channel left.
        Ok(()) | Err(_) => ExitCode::from(FAULTED),
    }
}

/// Run the terminal face, or its smoke face, writing its types and values in
/// `spelling`, and choose the exit code.
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
/// - witness: `tests::cli::smoke_is_terminal_free_but_interactive_tui_refuses_pipes`
/// - witness: `tests::cli::unwritable_standard_output_exits_two`
#[spec(ensures: |ret| ret == ExitCode::SUCCESS || ret == ExitCode::from(FAULTED))]
fn tui(
    screen: Screen,
    spelling: Spelling,
) -> ExitCode
{
    let attached = std::io::stdin().is_terminal() && std::io::stdout().is_terminal();
    let noted = match (screen, attached) {
        (Screen::Smoke, _) => match gandr_surface_tui::run_smoke(&mut std::io::stdout().lock()) {
            Ok(Ended::Completed) => return ExitCode::SUCCESS,
            Ok(Ended::Faulted(fault)) => writeln!(std::io::stderr(), "gandr: {fault}"),
            Err(error) => writeln!(std::io::stderr(), "gandr: cannot write the output: {error}"),
        },
        (Screen::Terminal, false) => writeln!(
            std::io::stderr(),
            "gandr: the terminal face needs a terminal on standard input and output; `gandr repl` reads a pipe"
        ),
        (Screen::Terminal, true) => match gandr_surface_tui::run(spelling) {
            Ok(Ended::Completed) => return ExitCode::SUCCESS,
            Ok(Ended::Faulted(fault)) => writeln!(std::io::stderr(), "gandr: {fault}"),
            Err(error) => writeln!(std::io::stderr(), "gandr: the terminal failed: {error}"),
        },
    };
    match noted {
        // When standard error is unwritable too, the exit code is the one
        // channel left.
        Ok(()) | Err(_) => ExitCode::from(FAULTED),
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
/// - witness: `tests::cli::unwritable_standard_output_exits_two`
#[spec(ensures: |ret| ret == ExitCode::SUCCESS || ret == ExitCode::from(FAULTED))]
fn capabilities() -> ExitCode
{
    let mut stdout = std::io::stdout().lock();
    let written = writeln!(stdout, "{Capabilities}").and_then(|()| stdout.flush());
    match written {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            match writeln!(std::io::stderr(), "gandr: cannot write the output: {error}") {
                Ok(()) | Err(_) => ExitCode::from(FAULTED),
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
/// - witness: `tests::cli::a_malformed_invocation_exits_two`
/// - witness: `tests::cli::help_exits_zero`
/// - witness: `tests::cli::unwritable_standard_output_exits_two`
/// - witness: `tests::cli::status_and_version_identify_the_same_build`
#[spec(ensures: |ret| ret == ExitCode::from(FAULTED)
    || (!error.use_stderr() && ret == ExitCode::SUCCESS))]
fn usage(error: &clap::Error) -> ExitCode
{
    match (error.print(), error.use_stderr()) {
        (Ok(()), false) => ExitCode::SUCCESS,
        (Ok(()), true) | (Err(_), _) => ExitCode::from(FAULTED),
    }
}

/// Refuse a `--grant` naming an operation the host does not declare.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one line on standard error, `gandr: --grant: no host interface
///   offers` and the operation in backticks, or the host table's own conflict;
///   exits `2`, a malformed invocation, whether or not the line could be
///   written.
/// - provides: the exit of a grant the host cannot give.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — an undeclared operation exits two naming it, before any
///   source is read.
/// - witness: `tests::cli::a_grant_bounds_held_capabilities_and_refuses_an_unknown_operation`
#[spec(ensures: |ret| ret == ExitCode::from(FAULTED))]
fn ungranted(refused: &AuthorityError) -> ExitCode
{
    let mut stderr = std::io::stderr().lock();
    let _written = match *refused {
        AuthorityError::Undeclared(ref operation) => writeln!(
            stderr,
            "gandr: --grant: no host interface offers `{}`",
            operation.as_ref()
        ),
        AuthorityError::Restriction(_) | AuthorityError::Conflict(_) => {
            writeln!(stderr, "gandr: --grant: the host's interfaces conflict")
        },
    };
    ExitCode::from(FAULTED)
}

/// Refuse a verb that has no paths to walk.
///
/// # Specification
/// - requires: nothing.
/// - ensures: one line on standard error, `gandr:` and why no package was found
///   from the working directory, or why the workspace the verb works on names
///   none; exits `2`, a malformed invocation, whether or not the line could be
///   written.
/// - provides: the exit of `check`, `test` or `fmt` run with no path where no
///   package or workspace is, or in a workspace that names no packages.
/// - fails: never.
/// - panics: none.
///
/// # Adequacy
/// - hypothesis: L3 — `check` with no path in a directory with no library above
///   it, and in a workspace naming a directory that roots no package, each
///   exits two before any source is read.
/// - witness: `tests::cli::a_verb_with_no_path_checks_the_package_it_runs_in_2687`
/// - witness: `tests::cli::a_workspace_checks_each_member_it_names_2687`
#[spec(ensures: |ret| ret == ExitCode::from(FAULTED))]
fn unpathed(unpathed: &Unpathed) -> ExitCode
{
    let mut stderr = std::io::stderr().lock();
    let _written = writeln!(stderr, "gandr: {unpathed}");
    ExitCode::from(FAULTED)
}

/// Render `outcome` and choose the exit code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: the status prints one line naming the driver's version. A walk
///   prints, for each source, each diagnostic the dispatcher's `entries` yields
///   for its step under the verb, laid out by `gandr-surface-render-terminal`:
///   each refusal, unsettled declaration and goal as a plain source snippet
///   followed by an empty line, and each ledger line — a settled fixture or a
///   pending source's refusal under `test`, a pending source the lowering read
///   — prefixed with its path. Each path the walk cannot carry through the
///   pipeline is a line on standard error. A walk under `check` then reconciles
///   the manifest of each of `packages`, as [`run`] does. The run's report and
///   its verdict close standard output, and the exit code is the verdict's, or
///   a manifest's when that is worse. A script follows [`script`]: what it
///   prints goes to standard output, its diagnostics to standard error and its
///   run status chooses the exit. A staging follows [`stage`], a formatting
///   [`fmt`], a ledger task [`ledger`], and a census [`cells`].
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
/// - witness: `tests::cli::a_settled_run_exits_zero`
/// - witness: `tests::cli::an_unsettled_run_exits_one`
/// - witness: `tests::cli::goals_report_an_obligation_without_failing`
/// - witness: `tests::cli::the_test_verb_prints_every_fixture_and_pending_source`
/// - witness: `tests::cli::an_unreadable_path_exits_two`
/// - witness: `tests::cli::a_failed_diagnostic_stream_stops_later_output`
/// - witness: `tests::cli::every_width_stages_the_serial_run`
/// - witness: `tests::cli::fmt_rewrites_what_check_reports`
/// - witness: `tests::cli::a_package_s_manifest_is_written_and_drift_refused_2687`
/// - witness: `tests::cli::cells_reports_each_hole_s_count`
#[spec(captures: [status = matches!(outcome, Outcome::Status(_)), script = matches!(outcome, Outcome::Script(_))],
    ensures: |ref ret| ret.as_ref().map_or(true, |exit|
        (script || *exit == ExitCode::SUCCESS || *exit == ExitCode::from(UNSETTLED) || *exit == ExitCode::from(FAULTED))
            && (!status || *exit == ExitCode::SUCCESS)))]
fn render(
    outcome: Outcome,
    printing: Printing,
    packages: &[Package],
    stdout: &mut dyn std::io::Write,
    stderr: &mut dyn std::io::Write,
) -> std::io::Result<ExitCode>
{
    match outcome {
        Outcome::Status(report) => {
            writeln!(stdout, "gandr {} — {report}", env!("CARGO_PKG_VERSION"))?;
            Ok(ExitCode::SUCCESS)
        },
        // The driver's pool: one per process, at the verb's width, its threads
        // started on the first fork of two items or more.
        Outcome::Run {
            verb,
            lints,
            walk,
            width,
        } => run(
            Pass {
                verb,
                lints,
                packages,
            },
            walk,
            &Pool::new(width),
            printing,
            stdout,
            stderr,
        ),
        Outcome::Script(mut runnable) => script(&mut runnable, printing.spelling, stdout, stderr),
        Outcome::Stage(staging) => {
            let pool = Pool::new(staging.width());
            stage(staging, &pool, stdout, stderr)
        },
        Outcome::Format(formatting) => {
            let pool = Pool::new(formatting.width());
            fmt(formatting, &pool, stdout, stderr)
        },
        Outcome::Ledger(task) => ledger(&task, stdout, stderr),
        Outcome::Cells(census) => cells(census, stdout, stderr),
    }
}

/// Run `task`: write its ledger, printing the path of each file written,
/// verify its exemplars, printing each that does not hold, sweep them for
/// recovery, printing each mutant marked elsewhere, or read the features
/// ledger, printing what was asked; and choose the exit code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each file written is its path, as one line on standard output, in
///   the order the task writes them, and the exit is zero. A verification
///   prints each exemplar that does not hold as `<path>: <fault>`, then the
///   count verified and found, on standard output; a recovery sweep prints its
///   near-miss table, each mutant marked elsewhere, then the count swept. Each
///   exits zero when nothing was found and one otherwise. A list prints each
///   feature it matched as `<id> [<status>] <name>: <line>`, a show prints the
///   feature's row, its exemplars' sources and its corpus paths, and both exit
///   zero. A ledger that cannot be generated, written, listed, read or answer
///   is `gandr: <fault>` on standard error and exits two.
/// - provides: `gandr ledger syntax --write <directory>`, `gandr ledger
///   exemplars <directory>`, `gandr ledger recovery <directory>`, `gandr ledger
///   list` and `gandr ledger show <id>`.
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
    *exit == ExitCode::SUCCESS || *exit == ExitCode::from(UNEXEMPLIFIED) || *exit == ExitCode::from(FAULTED)))]
fn ledger(
    task: &LedgerTask,
    stdout: &mut dyn std::io::Write,
    stderr: &mut dyn std::io::Write,
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
                ExitCode::from(UNEXEMPLIFIED)
            })
        },
        Ok(LedgerRun::Swept(report)) => {
            writeln!(stdout, "{report}")?;
            Ok(if report.findings().is_empty() {
                ExitCode::SUCCESS
            }
            else {
                ExitCode::from(UNEXEMPLIFIED)
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
            writeln!(stderr, "gandr: {fault}")?;
            Ok(ExitCode::from(FAULTED))
        },
    }
}

/// Lay out `formatting`'s sources on `pool`, printing the path of each whose
/// layout changed, and choose the exit code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each source whose layout changed is its path, as one line on
///   standard output, in walk order: written back under `fmt`, untouched under
///   `fmt --check`. A source already in layout prints nothing. Each path that
///   cannot be read or written back, names no source, or holds a source the
///   formatter refuses is `gandr: <path>: <fault>` on standard error, and the
///   formatting continues past it. Each declaration of a laid-out source that
///   kept its spelling because a rewrite would have changed what it lowers to
///   is ``gandr: <path>:<line>:<column>: `<name>` keeps its spelling:
///   <reason>`` on standard error, after the source's path if any, and changes
///   no exit. The exit is two when any path faulted; otherwise one under `fmt
///   --check` when any source is out of layout, and zero. Every byte written,
///   every source rewritten and the exit are the same at every width.
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
///   each distinguished; a sugared match over a stated sum keeps nothing.
///   Formatter refusals, unwritable sources and a withdrawn declaration's line
///   are outside these fixtures: no rewrite of the table changes what a corpus
///   source lowers to, and the formatter's own tests withdraw one.
/// - witness: `tests::cli::fmt_rewrites_what_check_reports`
/// - witness: `tests::cli::fmt_sugars_a_match_over_a_stated_sum_791`
#[spec(captures: [checking = formatting.rewrite() == Rewrite::Check],
    ensures: |ref ret| ret.as_ref().map_or(true, |exit|
        *exit == ExitCode::SUCCESS || *exit == ExitCode::from(FAULTED)
            || (checking && *exit == ExitCode::from(UNFORMATTED))))]
fn fmt(
    formatting: Formatting,
    pool: &Pool,
    stdout: &mut dyn std::io::Write,
    stderr: &mut dyn std::io::Write,
) -> std::io::Result<ExitCode>
{
    let rewrite = formatting.rewrite();
    let (mut changed, mut faulted) = (false, false);
    let visited = formatting.visit(pool, |step| {
        let written = match step {
            FormatStep::Unchanged { path, withdrawn } => kept(stderr, path, &withdrawn),
            FormatStep::Changed { path, withdrawn } => {
                changed = true;
                writeln!(stdout, "{}", path.display()).and_then(|()| kept(stderr, path, &withdrawn))
            },
            FormatStep::Fault { path, fault } => {
                faulted = true;
                writeln!(stderr, "gandr: {}: {fault}", path.display())
            },
        };
        match written {
            Ok(()) => ControlFlow::Continue(()),
            Err(error) => ControlFlow::Break(error),
        }
    });
    if let ControlFlow::Break(error) = visited {
        return Err(error);
    }
    Ok(match (faulted, changed, rewrite) {
        (true, ..) => ExitCode::from(FAULTED),
        (false, true, Rewrite::Check) => ExitCode::from(UNFORMATTED),
        (false, false, _) | (false, true, Rewrite::InPlace) => ExitCode::SUCCESS,
    })
}

/// Print each declaration of the source at `path` that kept its spelling as
/// ``gandr: <path>:<line>:<column>: `<name>` keeps its spelling: <reason>``.
///
/// # Specification
/// trivial.
fn kept(
    stderr: &mut dyn std::io::Write,
    path: &std::path::Path,
    withdrawn: &[Kept],
) -> std::io::Result<()>
{
    for declaration in withdrawn {
        writeln!(stderr, "gandr: {}:{declaration}", path.display())?;
    }
    Ok(())
}

/// Step `census`, printing each cell of each source on a line, and choose the
/// exit code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: each cell of each source the census reads is `<path>:<row>` on
///   standard output, the row rendered as the dispatcher's `CellRow` renders
///   it, sources in walk order and each source's cells in the census's. Each
///   path the census cannot read is `gandr: <path>: <fault>` on standard error,
///   and the census continues past it. The exit is two when any path faulted,
///   and zero otherwise.
/// - provides: `gandr cells`.
/// - fails: the first write error on either stream, printing nothing after it
///   and reading no source after it.
/// - panics: none.
///
/// # Errors
/// The [`std::io::Error`] of the first write that failed.
///
/// # Adequacy
/// - hypothesis: L3 — the corpus exemplar beside a missing path observes every
///   line on both streams and the exit; dropping a row, a fault, or the fault's
///   exit changes the observation.
/// - witness: `tests::cli::cells_reports_each_hole_s_count`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |exit|
    *exit == ExitCode::SUCCESS || *exit == ExitCode::from(FAULTED)))]
fn cells(
    mut census: Census,
    stdout: &mut dyn std::io::Write,
    stderr: &mut dyn std::io::Write,
) -> std::io::Result<ExitCode>
{
    let mut faulted = false;
    while let Maybe::Present(step) = census.step() {
        match step {
            CensusStep::Source { path, cells } => {
                for row in &cells {
                    writeln!(stdout, "{}:{row}", path.display())?;
                }
            },
            CensusStep::Fault { path, fault } => {
                faulted = true;
                writeln!(stderr, "gandr: {}: {fault}", path.display())?;
            },
        }
    }
    Ok(if faulted {
        ExitCode::from(FAULTED)
    }
    else {
        ExitCode::SUCCESS
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
/// - witness: `tests::cli::every_width_stages_the_serial_run`
/// - witness: `tests::cli::a_malformed_invocation_exits_two`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |exit|
    *exit == ExitCode::SUCCESS || *exit == ExitCode::from(REFUSED) || *exit == ExitCode::from(FAULTED)))]
fn stage(
    staging: Staging,
    pool: &Pool,
    stdout: &mut dyn std::io::Write,
    stderr: &mut dyn std::io::Write,
) -> std::io::Result<ExitCode>
{
    let run = match staging.run(pool) {
        Ok(run) => run,
        Err(fault) => {
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
        StageVerdict::Readmitted => ExitCode::SUCCESS,
        StageVerdict::Refused => ExitCode::from(REFUSED),
        StageVerdict::Faulted => ExitCode::from(FAULTED),
    })
}

/// Visit `walk` on `pool` under the pass's verb, printing each step at the
/// verbosity and in the spelling `printing` names, then each manifest the
/// pass's packages reconcile, then the report and the verdict.
///
/// # Specification
/// - requires: nothing.
/// - ensures: consumes the walk, writing each step in walk order: each
///   diagnostic the dispatcher's `entries` yields for a source step under
///   `verb`, each lint reaching where `lints` says, laid out by
///   `gandr-surface-render-terminal`, to standard output at `verbosity` with
///   every type in `spelling` — below the JSON level a report as a plain
///   snippet followed by an empty line and a ledger line as itself, at it each
///   entry as one line of JSON — and each fault as one `gandr: <path>: <fault>`
///   line to standard error. Under `check`, each package of the pass whose
///   library settled with no refusal has its manifest read from the library's
///   program and reconciled: each written, rewritten or unchanged is the line
///   `manifest: <path>: <what>` on standard output, at the JSON level an object
///   whose `level` is `manifest`; a library that states no manifest, and a
///   manifest refused as drift, are each `gandr: <path>: <why>` on standard
///   error and unsettle the run, and one that cannot be read or written faults
///   it. Then the final report and verdict, at the JSON level as one object
///   whose `level` is `summary`. The exit is zero for settled, one for
///   unsettled and two for faulted, as the walk's final report decides under
///   the offered verb, or a manifest when that is worse, at every verbosity.
///   Every byte written and the exit are the same at every width.
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
/// - witness: `tests::cli::an_unreadable_path_exits_two`
/// - witness: `tests::cli::the_test_verb_prints_every_fixture_and_pending_source`
/// - witness: `tests::cli::a_failed_diagnostic_stream_stops_later_output`
/// - witness: `tests::cli::every_width_prints_the_serial_run`
/// - witness: `tests::cli::verbosity_chooses_how_much_of_a_report_prints`
/// - witness: `tests::cli::a_lint_reports_each_inferred_exit_and_its_fix_settles_it`
/// - witness: `tests::cli::a_package_s_manifest_is_written_and_drift_refused_2687`
#[spec(ensures: |ref ret| ret.as_ref().map_or(true, |exit|
    *exit == ExitCode::SUCCESS || *exit == ExitCode::from(UNSETTLED) || *exit == ExitCode::from(FAULTED)))]
fn run(
    pass: Pass<'_>,
    walk: Walk,
    pool: &Pool,
    printing: Printing,
    stdout: &mut dyn std::io::Write,
    stderr: &mut dyn std::io::Write,
) -> std::io::Result<ExitCode>
{
    let Pass {
        verb,
        lints,
        packages,
    } = pass;
    let Printing {
        verbosity,
        spelling,
    } = printing;
    let checking = matches!(verb, Verb::Check(_));
    // The manifest each package's library states, by the package's place.
    let mut manifests: Vec<Option<Result<Manifest, Unmanifested>>> =
        packages.iter().map(|_| None).collect();
    let visited = walk.visit(pool, |mut step| {
        match step {
            Step::Source { .. } => {
                for diagnostic in entries(&step, verb).linting(lints).spelling(spelling) {
                    let separator = match (diagnostic.severity, verbosity) {
                        (
                            Severity::Error | Severity::Warning | Severity::Goal | Severity::Note,
                            Verbosity::User | Verbosity::Detailed | Verbosity::Debug,
                        ) => "\n",
                        (
                            Severity::Error | Severity::Warning | Severity::Goal | Severity::Note,
                            Verbosity::Json,
                        )
                        | (Severity::Ledger, _) => "",
                    };
                    let written = writeln!(
                        stdout,
                        "{}{separator}",
                        gandr_surface_render_terminal::render(
                            &diagnostic,
                            RenderStyle::Plain,
                            verbosity
                        )
                    );
                    if let Err(error) = written {
                        return ControlFlow::Break(error);
                    }
                }
                if checking {
                    read_manifest(&mut step, packages, &mut manifests);
                }
            },
            Step::Fault { path, fault } => {
                if let Err(error) = writeln!(stderr, "gandr: {}: {fault}", path.display()) {
                    return ControlFlow::Break(error);
                }
            },
        }
        ControlFlow::Continue(())
    });
    let report = match visited {
        ControlFlow::Continue(report) => report,
        ControlFlow::Break(error) => return Err(error),
    };
    let mut verdict = report.verdict(verb);
    for (package, manifest) in packages.iter().zip(manifests) {
        if let Some(manifest) = manifest {
            let reached = manifested(package, manifest, verbosity, stdout, stderr)?;
            verdict = worse(verdict, reached);
        }
    }
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
        RunVerdict::Settled => ExitCode::SUCCESS,
        RunVerdict::Unsettled => ExitCode::from(UNSETTLED),
        RunVerdict::Faulted => ExitCode::from(FAULTED),
    })
}

/// Reconcile `package`'s manifest with what its library states, printing what
/// came of it, and the verdict it leaves the run at.
///
/// # Specification
/// - requires: `manifest` is what `package`'s library states.
/// - ensures: a library that states no manifest is `gandr: <library>: <why>` on
///   standard error and unsettles the run. Otherwise the manifest is reconciled
///   at `package`'s root: written, rewritten or unchanged is `manifest: <path>:
///   <what>` on standard output, at the JSON level an object whose `level` is
///   `manifest`, and settles; drift is `gandr: <path>: <why>` on standard error
///   and unsettles; a file that cannot be read or written likewise, and faults.
/// - provides: the manifest step `run` takes for each package.
/// - fails: the first write error on either stream.
/// - panics: none.
/// - executable: none — the outcome is the file's on disk and the streams'
///   bytes, which the CLI witnesses observe.
///
/// # Errors
/// The [`std::io::Error`] of the first write that failed.
///
/// # Adequacy
/// - hypothesis: L3 — a manifest written, unchanged, rewritten and drifted, and
///   a library stating no version, each print and exit as stated.
/// - witness: `tests::cli::a_package_s_manifest_is_written_and_drift_refused_2687`
fn manifested(
    package: &Package,
    manifest: Result<Manifest, Unmanifested>,
    verbosity: Verbosity,
    stdout: &mut dyn std::io::Write,
    stderr: &mut dyn std::io::Write,
) -> std::io::Result<RunVerdict>
{
    let manifest = match manifest {
        Ok(manifest) => manifest,
        Err(unmanifested) => {
            writeln!(
                stderr,
                "gandr: {}: {unmanifested}",
                package.library().display()
            )?;
            return Ok(RunVerdict::Unsettled);
        },
    };
    let path = package.manifest();
    match reconcile(&path, &manifest) {
        Ok(reconciled) => {
            if verbosity == Verbosity::Json {
                let line = serde_json::json!({
                    "level": "manifest",
                    "path": path.display().to_string(),
                    "reconciled": reconciled.to_string(),
                });
                writeln!(stdout, "{line}")?;
            }
            else {
                writeln!(stdout, "manifest: {}: {reconciled}", path.display())?;
            }
            Ok(RunVerdict::Settled)
        },
        Err(fault) => {
            writeln!(stderr, "gandr: {}: {fault}", path.display())?;
            Ok(match fault {
                ManifestFault::Drifted => RunVerdict::Unsettled,
                ManifestFault::Io(_) => RunVerdict::Faulted,
            })
        },
    }
}

/// Read the manifest a package's library states, when `step` is that library
/// and settled, into the package's place in `manifests`.
///
/// # Specification
/// - requires: `manifests` holds one place per package, in order.
/// - ensures: a settled source step whose canonical path is the library of a
///   package has that package's place set to [`Manifest::of`] its program, its
///   report of the library's own declarations, and the package; any other step
///   changes nothing.
/// - provides: the manifest `run` reconciles after the walk.
/// - fails: never; a library that states no manifest is the place's error.
/// - panics: none.
/// - executable: none — the clause is the body's one match; the CLI witness
///   observes the manifest written from the library and none from an unsettled
///   one.
///
/// # Adequacy
/// - hypothesis: L3 — a package checked whole writes the manifest its library
///   states, one whose library is unsettled writes none, and two libraries
///   sharing an import each write their own.
/// - witness: `tests::cli::a_package_s_manifest_is_written_and_drift_refused_2687`
/// - witness: `tests::cli::a_workspace_checks_each_member_it_names_2687`
fn read_manifest(
    step: &mut Step<'_>,
    packages: &[Package],
    manifests: &mut [Option<Result<Manifest, Unmanifested>>],
)
{
    let Step::Source {
        path,
        standing: Standing::Settled,
        composed:
            Composed::Settled {
                ref mut program,
                ref report,
                ..
            },
        ..
    } = *step
    else {
        return;
    };
    if path.file_name().is_none_or(|name| name != LIBRARY) {
        return;
    }
    let Ok(canonical) = path.canonicalize()
    else {
        return;
    };
    if let Some(place) = packages
        .iter()
        .position(|package| package.library() == canonical)
        && let (Some(package), Some(slot)) = (packages.get(place), manifests.get_mut(place))
    {
        *slot = Some(Manifest::of(program, report, package));
    }
}

/// The worse of two verdicts: a fault outranks an unsettled run, which
/// outranks a settled one.
///
/// # Specification
/// trivial.
const fn worse(
    one: RunVerdict,
    other: RunVerdict,
) -> RunVerdict
{
    match (one, other) {
        (RunVerdict::Faulted, _) | (_, RunVerdict::Faulted) => RunVerdict::Faulted,
        (RunVerdict::Unsettled, _) | (_, RunVerdict::Unsettled) => RunVerdict::Unsettled,
        (RunVerdict::Settled, RunVerdict::Settled) => RunVerdict::Settled,
    }
}

/// Run `runnable`, its types written in `spelling`, printing what it prints on
/// standard output and everything else on standard error, and choose the exit
/// code.
///
/// # Specification
/// - requires: nothing.
/// - ensures: a path that cannot be read as one source is `gandr: <path>:
///   <fault>` on standard error. Otherwise every report `gandr check --goals`
///   prints for the source, its types in `spelling`, goes to standard error as
///   a plain snippet followed by an empty line, and every ledger line beside
///   them; then a source declaring an entry runs it and writes nothing but the
///   lines it prints, each written to standard output as it runs. A run blamed,
///   stuck or unfinished, and an entry that reaches a declaration the machine
///   carries no image of, is one line on standard error: `gandr:`, the path,
///   the entry's name in backticks and the evaluation's spelling. A source
///   carrying a refusal is `gandr: <path>: refused; nothing ran`, and one
///   declaring no `main` at its top level runs nothing — not its last
///   declaration — and is one line on standard error naming `def main` and
///   pointing at `gandr check` and `gandr test`. The exit code is an entry's
///   exit status when it returned or exited with one; otherwise `1` for a run
///   that stopped short of one, and `2` for a script that never reached the
///   machine.
/// - provides: `gandr run`, with what it prints on the one stream a caller
///   reads.
/// - fails: the first write error on either stream.
/// - panics: none.
/// - executable: none — the exit code is the process's status, which the
///   witnesses observe by spawning the binary.
///
/// # Errors
/// The [`std::io::Error`] of the first write that failed.
///
/// # Adequacy
/// - hypothesis: L3 — an entry, blame, type refusal, unrelated declaration
///   refusal, absent source and a source declaring no `main` are observed
///   through exact status, printed lines and separate diagnostic streams. Wrong
///   status, repeated lines or evaluation after refusal changes these
///   observations. Arbitrary machine programs and interruption timing are
///   outside them. An entry returning a code, one exiting through `Proc.exit`,
///   one counting its arguments and one reaching a goal observe the entry's
///   statuses.
/// - witness: `tests::cli::a_script_that_runs_its_main_leaves_successfully`
/// - witness: `tests::cli::a_script_that_blames_leaves_with_a_failure_status`
/// - witness: `tests::cli::an_ill_typed_script_is_refused_by_the_checker`
/// - witness: `tests::cli::an_outcome_only_refusal_is_visible_in_a_script_run`
/// - witness: `tests::cli::an_absent_script_is_refused_by_path`
/// - witness: `tests::cli::a_script_with_no_program_is_refused`
/// - witness: `tests::cli::a_failed_diagnostic_stream_stops_later_output`
/// - witness: `tests::cli::a_program_leaves_with_its_entry_s_status_1881`
/// - witness: `tests::cli::a_program_prints_hello_world_2279`
fn script(
    runnable: &mut Script,
    spelling: Spelling,
    stdout: &mut dyn std::io::Write,
    stderr: &mut dyn std::io::Write,
) -> std::io::Result<ExitCode>
{
    let ran = runnable.run(&mut Lines { out: &mut *stdout });
    let status = ran.status();
    let mut exited = None;
    match ran {
        ScriptRun::Fault { path, fault } => {
            writeln!(stderr, "gandr: {}: {fault}", path.display())?;
        },
        ScriptRun::Source { step, ran } => {
            for diagnostic in entries(&step, Verb::Check(Goals::Reported)).spelling(spelling) {
                let rendered = gandr_surface_render_terminal::render(
                    &diagnostic,
                    RenderStyle::Plain,
                    Verbosity::User,
                );
                match diagnostic.severity {
                    Severity::Error | Severity::Warning | Severity::Goal | Severity::Note => {
                        writeln!(stderr, "{rendered}\n")?;
                    },
                    Severity::Ledger => writeln!(stderr, "{rendered}")?,
                }
            }
            let (path, text) = match step {
                Step::Source { path, ref text, .. } => (path.display(), text.as_ref()),
                Step::Fault { path, .. } => (path.display(), ""),
            };
            match ran {
                Ran::Entered {
                    entered: Entered::Exited(code),
                    ..
                } => exited = Some(u8::from(code)),
                Ran::Entered {
                    target,
                    entered: Entered::Ended(Evaluation::Holed { at, .. }),
                } => {
                    // The hole as the source writes it, and its line and
                    // column, counted from one.
                    let written = match at {
                        Maybe::Present(span) => text
                            .get(usize::from(span.start()) .. usize::from(span.end()))
                            .zip(text.get(.. usize::from(span.start()))),
                        Maybe::Absent(_) => None,
                    };
                    match written {
                        Some((hole, before)) => {
                            let line = before.matches('\n').count().saturating_add(1);
                            let column = before
                                .rsplit('\n')
                                .next()
                                .map_or(0, |last| last.chars().count())
                                .saturating_add(1);
                            writeln!(
                                stderr,
                                "gandr: {path}:{line}:{column}: `{target}` reached the hole `{hole}`"
                            )?;
                        },
                        None => writeln!(stderr, "gandr: {path}: `{target}` reached a hole")?,
                    }
                },
                Ran::Entered {
                    target,
                    entered: Entered::Ended(evaluation),
                } => {
                    writeln!(stderr, "gandr: {path}: `{target}` {evaluation}")?;
                },
                Ran::Refused => writeln!(stderr, "gandr: {path}: refused; nothing ran")?,
                Ran::NoProgram => writeln!(
                    stderr,
                    "gandr: {path}: declares no `main` to run; a program runs its `def main() -> \
                     Unit {{ … }}`, and a source of declarations alone is checked by `gandr \
                     check` or tested by `gandr test`"
                )?,
            }
        },
    }
    Ok(match (exited, status) {
        (Some(code), _) => ExitCode::from(code),
        (None, RunStatus::Value) => ExitCode::SUCCESS,
        (None, RunStatus::Failed) => ExitCode::from(STOPPED),
        (None, RunStatus::Unreached) => ExitCode::from(UNREACHED),
    })
}

/// The console `gandr run` hands a program: each line it prints written to
/// `out`, standard output, as one line.
#[repr(transparent)]
struct Lines<'out>
{
    /// Where the lines go.
    out: &'out mut dyn std::io::Write,
}

impl Console for Lines<'_>
{
    /// Write `line` and a newline to `out`.
    ///
    /// # Specification
    /// trivial.
    fn print(
        &mut self,
        line: Line<'_>,
    ) -> Printed
    {
        match writeln!(self.out, "{}", line.as_ref()) {
            Ok(()) => Printed::Written,
            Err(_) => Printed::Failed,
        }
    }
}
