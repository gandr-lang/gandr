# gandr-lang

The `gandr` binary, the entry point of the gandr language toolchain: `gandr check` and `gandr test` over gandr sources, with the run's verdict as the exit code, `gandr run`, a source run as a program, `gandr lsp`, the language server, `gandr repl`, the read-evaluate loop, and `gandr tui`, the same loop full-screen.

<!-- toc -->

- [Synopsis](#synopsis)
- [Verbs](#verbs)
- [Exit codes](#exit-codes)
- [Examples](#examples)
- [Output the driver cannot write is a fault](#output-the-driver-cannot-write-is-a-fault)
- [Tests: the floor and the deferred rows](#tests-the-floor-and-the-deferred-rows)
- [Optional tracing](#optional-tracing)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** The package `gandr-lang` builds the `gandr` binary. `gandr check <paths>` settles every declaration of every source under the paths given and prints each unsettled one; `gandr test <paths>` runs the same pass and also prints every fixture and every pending source. `gandr run <file>` checks one source as `check` does, runs the last name it declares on the L machine, and prints the value. `gandr lsp` serves `gandr-surface-lsp`'s language server on standard input and output until the client sends `exit`, and `gandr lsp --capabilities` prints what the server advertises. `gandr repl` runs `gandr-surface-repl`'s read-evaluate loop on standard input and output: the line editor on a terminal, a plain transcript when standard input is piped or under `--batch`. `gandr tui` runs the same loop through `gandr-surface-tui`'s terminal face, full-screen, and `gandr tui --smoke` runs that face once off-screen and prints `gandr tui: ready`. A bare `gandr` prints one status line naming the driver version and stating that toolchain management is not implemented.

**Why.** The driver owns the argument surface and the process boundary, and routes everything after that through `gandr-surface-dispatcher`, which composes the pipeline and decides the gate without a process. The registry name `gandr` belongs to an unrelated crate, so the package is `gandr-lang` and the binary is `gandr`.

**How.** `clap` parses the arguments before anything is written. The invocation is dispatched; the driver advances the walk the dispatcher returns, prints each source step's entries as `gandr-surface-diagnostics` renders them, and each fault, then the runner's report and its verdict, through locked handles and fallible `writeln!`, and returns the verdict as its exit code from `main`. `gandr run` runs the dispatcher's `Script`, writes the value alone to standard output and everything else to standard error, and returns the run's status as its exit code. `gandr lsp` hands the locked standard streams to `gandr-surface-lsp`'s `serve` and returns how the session ended as its exit code; `gandr repl` hands them to `gandr-surface-repl`'s `run_batch` or `run_interactive` and returns how the loop ended; `gandr tui` checks that standard input and output are a terminal, then hands the terminal to `gandr-surface-tui`'s `run`, or standard output to its `run_smoke` under `--smoke`, and returns how the face ended. Witnesses, each spawning the binary: `cli::cli::a_settled_run_exits_zero`, `cli::cli::an_unsettled_run_exits_one`, `cli::cli::an_unreadable_path_exits_two`, `cli::cli::a_malformed_invocation_exits_two`, `cli::cli::unwritable_standard_output_exits_two`, `cli::cli::goals_report_an_obligation_without_failing`, `cli::cli::the_test_verb_prints_every_fixture_and_pending_source`, `cli::cli::help_exits_zero`, `cli::cli::a_bare_invocation_prints_the_status`, `cli::cli::lsp_capabilities_print_one_line_of_json`, `cli::cli::lsp_serves_a_session_over_the_standard_streams`, `cli::cli::a_piped_repl_session_prints_its_transcript`, `cli::cli::the_tui_smoke_face_prints_ready`, `cli::cli::the_tui_needs_a_terminal`, and for `gandr run` the rows [below](#tests-the-floor-and-the-deferred-rows).

## Verbs

| Invocation | Prints | Fails on |
| ---------- | ------ | -------- |
| `gandr check <paths>` | each unsettled declaration, each source refused as a whole | any unsettled declaration |
| `gandr check --goals <paths>` | as `check`, a declaration unsettled by its obligations alone marked `goal:` | any unsettled declaration but those |
| `gandr test <paths>` | as `check`, plus every fixture, settled or not, and every pending source's refusal | as `check` |
| `gandr run <file>` | the value, alone, on standard output; every report `check --goals` would print, and why a run stopped or never started, on standard error | a run blamed or stuck, or a source that never reached the machine |
| `gandr lsp` | the language server's frames on standard output, until `exit` | a session ended before `shutdown` |
| `gandr lsp --capabilities` | the `initialize` result as one line of JSON | nothing |
| `gandr repl` | the line editor's prompt on a terminal; piped, each submission's echo and its lines, as a plain transcript | a fault that stops the loop |
| `gandr repl --batch` | the plain transcript, even on a terminal | as `repl` |
| `gandr tui` | the transcript, an input pane and a status line, full-screen on the terminal | a fault that stops the face, a terminal that fails, or no terminal |
| `gandr tui --smoke` | `gandr tui: ready` | a fault that stops the face |

A path is a source file of any name, or a directory searched for `.gandr` sources. The directories a source sits in decide its root — `strict`, `fixture`, or `fixture/pending` — and a source under none is strict ([membership is location](../surface-dispatcher/README.md#membership-is-location)). A refusal, an unsettled declaration and a goal each print as a located source snippet — the class and message, the path with line and column, the lines the report covers with their marks — followed by a blank line ([what a report shows](../surface-diagnostics/README.md#what-a-report-shows)); a settled fixture, a pending source's refusal and a pending source the lowering reads each print one ledger line, `<path>: <report>`. The driver writes plain text, without colour. Each fault is `gandr: <path>: <fault>` on standard error. Every run closes standard output with the runner's report — the sources read by root, the lowerings, the goals, the exercised table, the ledger size, the declaration and fixture counts, the surviving obligations, the refusals by class, the run's settlement and its seal — and `verdict: settled`, `unsettled` or `faulted`.

`gandr run` takes exactly one path, `-` among them: there is no standard-input face for it to name. The source is composed under the root its path classifies as and runs only when no declaration of it was refused; its target is the last name it declares ([the run stage](../surface-dispatcher/README.md#the-run-stage-follows-the-check)). A completed run writes its value as the one line of standard output, spelled as a `runs` expectation states it, so a caller reads the value without parsing anything else; the prior implementation's script runner could not hand its value to its caller. A run blamed on a goal, stuck or unfinished is `` gandr: <path>: `<target>` <what it came to> `` on standard error; a source carrying a refusal is `gandr: <path>: refused; nothing ran` after its reports, and one declaring no name `gandr: <path>: declares no name to run`.

`gandr lsp` reads frames from standard input and writes every answer and notification to standard output; it rechecks a document whole at every synchronisation and publishes the same reports `gandr check --goals` prints for it, under the root its path classifies as ([the language server](../surface-lsp/README.md)). A stream that fails is `gandr: the language server stopped: <fault>` on standard error.

`gandr repl` reads declarations a line at a time and submits each buffer the parser reads as complete, judging it with every declaration kept before it, as `gandr check --goals` judges a strict source; a refused submission is shown and not kept. Each submission prints its echo after `▸`, a `name : T` line per declaration it checked followed by what running it came to — `= value`, `! blame`, or `·` and why it stopped or never ran — a `? name : T` line per goal, and each refusal as `gandr check` prints it — in colour only when the line editor runs and standard output is a terminal, plain otherwise. `:type <expression>`, `:load <file>`, `:reset`, `:help` and `:quit` speak to the loop ([the read-evaluate loop](../surface-repl/README.md)). A fault that stops the loop is `gandr: <fault>` on standard error.

`gandr tui` takes the terminal for the same loop: the transcript keeps the lines `gandr repl` prints, coloured by kind with the echo highlighted, above the line being edited; Enter submits, Ctrl-C drops the line and any waiting buffer, and Esc or `:quit` leaves and restores the terminal ([the terminal face](../surface-tui/README.md)). Without a terminal on standard input and output it draws nothing and notes `gandr: the terminal face needs a terminal on standard input and output` on standard error; `gandr tui --smoke` needs none. A fault that stops the face is `gandr: <fault>`, and a terminal that fails `gandr: the terminal failed: <error>`, on standard error.

## Exit codes

| Code | Meaning |
| ---- | ------- |
| `0` | every declaration settled, or a script's run returned a value; also `--help`, `--version`, a bare `gandr`, `gandr lsp --capabilities`, a language-server session ended by `exit` after `shutdown`, a read-evaluate loop that reached the end of its input or `:quit`, a terminal face the user left, and `gandr tui --smoke` |
| `1` | at least one declaration is unsettled, or a source was not read as its root expects; a script's run was blamed on a goal or stopped short of a value; also a language-server session ended by `exit`, or by its input closing, before `shutdown` |
| `2` | an engine fault, an unreadable path or one naming no source, a malformed invocation, output the driver could not write, a language-server stream that failed, a fault that stopped a read-evaluate loop or a terminal face, a terminal that failed, `gandr tui` without a terminal, or a script that never reached the machine: unreadable, refused, declaring no name, or running into a declaration the machine carries no image of |

A fault outranks an unsettled declaration: a run with both exits `2`. The walk continues past a faulted path, so every fault of a run is printed.

## Examples

```console
$ gandr check crates/surface-corpus/strict
sources: 2 read (2 strict, 0 fixture, 0 pending), 0 refused as a whole, 0 no longer pending, 0 faulted
lowerings: 2
goals: 0
exercised: a lambda checks 2; a return checks 3; …
ledger size: 0
declarations: 11 settled, 0 unsettled
fixtures: 0 settled, 0 unsettled
surviving obligations: 0 undeclared, 0 unproduced
refusals: 0 user absence, 0 unrepresentable, 0 malformed source, 0 engine fault
run: settled
seal: sealed
verdict: settled
$ gandr check broken.gandr
error[UnresolvedName]: no declaration or binder answers `missing` at 13..20
  ╭▸ broken.gandr:1:14
  │
1 │ def broken = missing ;
  │              ━━━━━━━ malformed source
  │
  ╰ note: unsettled `broken` states checks owing 0

sources: 1 read (1 strict, 0 fixture, 0 pending), 0 refused as a whole, 0 no longer pending, 0 faulted
…
verdict: unsettled
$ echo $?
1
$ printf 'def answer = 42 ;\n:type answer\n' | gandr repl
▸ def answer = 42 ;
answer : Integer
= 42
▸ :type answer
: Integer
$ gandr tui --smoke
gandr tui: ready
$ gandr run answer.gandr
42
$ gandr run blame.gandr
goal: `later` states checks owing 0; produced checks owing 1
  ╭▸ blame.gandr:1:1
  │
1 │ def later : +U (-F Integer) ;
  ╰╴━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ surviving obligations: 1 undeclared, 0 unproduced

gandr: blame.gandr: `main` blame: `later` is owed its body
$ echo $?
1
```

## Output the driver cannot write is a fault

`main` returns its exit code rather than a `Result`, so a write or flush that fails — a closed pipe, a full disk — is noted on standard error, when that is writable, and exits `2`, the code every fault shares. The runtime ignores `SIGPIPE`, so a reader that closed early surfaces as a failed write, not a signal. The alternative was returning the I/O error from `main`, whose runtime path exits `1` and would read as an unsettled run. The choice reverses if a fault class needs its own code, which would be a fourth row above.

## Tests: the floor and the deferred rows

Driver routing, rendering and nontrivial test helpers carry executable predicates and bounded adequacy arguments. Exit-code domains are checked on each call; a completed walk also compares its exit with its final report under the selected verb. No nontrivial item has an executable exemption. The predicates do not observe opaque output streams: the CLI witnesses observe exit status, protocol framing, diagnostic identity and location, stream separation, and value multiplicity instead of incidental English wording or a copy of the producer's formatter.

`scratch_ownership_keeps_simultaneous_cases_independent` runs two same-name sources in separate roots, removes one root and checks that the other still behaves independently. `a_failed_diagnostic_stream_stops_later_output` closes the diagnostic reader and verifies that neither a later summary nor a script value is emitted after that first write fails. Closed standard output covers status, check, run, help, capabilities, batch REPL and TUI smoke; a literal `-` is checked both absent and present in an owned directory.

The native command smoke additionally compares independently decoded LSP initialization and capability JSON, exercises script and batch entry points, and submits a declaration on a terminal before quitting and comparing its terminal settings. These finite observations do not claim arbitrary editor timing, terminal backends, source programs or failing filesystem coverage.

The prior implementation's script-runner rows over the pure fragment are the floor for `gandr run`, ported by name, each with the fragment's form of its script: `a_script_that_returns_a_value_leaves_successfully` (exit `0`, `42` alone on standard output), `a_script_that_blames_leaves_with_a_failure_status` (exit `1`), `an_ill_typed_script_is_refused_by_the_checker` (exit `2`), `an_outcome_only_refusal_is_visible_in_a_script_run`, `an_absent_script_is_refused_by_path`, `a_script_with_no_program_is_refused`, `a_second_operand_is_refused` and `a_bare_dash_is_a_path_not_standard_input`, under `cli::cli::`. The first three are the exit-code witnesses, and `cli::cli::the_value_of_a_run_is_printed_once` asserts the value is the whole of standard output. The prior script was a final expression and a source of declarations alone had no program; here the target is the last name declared, so the no-program row takes a source declaring nothing.

Deferred, with what each needs: `a_successful_script_reports_a_shadowing_warning`, a final expression and a shadowing warning; `a_script_that_exits_leaves_with_its_own_status`, `a_negative_exit_code_wraps_the_way_a_shell_wraps_it` and `an_out_of_range_exit_code_is_reduced_to_a_byte`, the process builtins; `a_script_routes_its_result_after_captured_tool_calls` and `a_script_whose_tool_cannot_spawn_leaves_with_a_failure_status`, effects and the tool host; `the_native_ffi_corpus_script_runs_through_the_cli`, `an_ffi_library_load_failure_is_a_failed_run`, `an_ffi_missing_symbol_is_a_failed_run` and `an_ffi_null_returned_string_is_a_failed_run`, foreign declarations. The prior rows for the bare invocation, help, the unknown flag, the terminal interface and the language server's legend belong to those faces, not to the script runner.

## Optional tracing

Build with `cargo build -p gandr-lang --features tracing` to report driver and dispatcher diagnostics on stderr. The feature forwards to `gandr-surface-dispatcher`; this driver has no evaluator dependency and does not activate evaluator tracing. A default build carries no tracing instrumentation or dependency: `cargo tree -p gandr-lang -e normal,build` lists neither `tracing` nor `tracing-subscriber` until the feature is on.

Argument parsing runs before subscriber installation, so help, version and argument errors retain their ordinary output. A scoped, thread-local subscriber reports dispatch-span completion and successful output flushing, then restores the prior subscriber when the invocation ends. Libraries install no subscriber. Standard-output write and flush errors remain faults rather than successful-completion events. Tracing diagnostics may precede a fault’s `gandr:` line on stderr; stdout and exit codes are unchanged.

The output backend is [`tracing-subscriber`](https://docs.rs/tracing-subscriber/0.3.23/tracing_subscriber/fmt/index.html) 0.3.23 with only `fmt` and its required registry/std support. ANSI formatting, the log bridge, filter parsing, JSON and time integrations stay off. This release includes the [ANSI-input escaping fix](https://rustsec.org/advisories/RUSTSEC-2025-0055); the current events contain fixed messages and no user payloads. A global subscriber was rejected because the invocation need not own process-wide diagnostics; an environment filter adds parsing machinery for no current CLI option. Revisit those choices when the driver gains a consumer requiring them, or the selected version needs a security or maintenance replacement.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
