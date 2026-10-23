# gandr-lang

The `gandr` binary, the entry point of the gandr language toolchain: `gandr check` and `gandr test` over gandr sources, with the run's verdict as the exit code, `gandr run`, a source run as a program, `gandr stage`, staged programs checked on every core, `gandr fmt`, sources laid out at a page width, `gandr ledger`, the language surface written out from the grammar and the features ledger read as a guide, `gandr lsp`, the language server, `gandr mcp`, the Model Context Protocol server, `gandr view`, the side view beside an editor, `gandr serve`, the engine hub their clients share, `gandr repl`, the read-evaluate loop, and `gandr tui`, the same loop full-screen.

<!-- toc -->
- [Synopsis](#synopsis)
- [Examples](#examples)
- [Where the detail lives](#where-the-detail-lives)
- [License](#license)
<!-- tocstop -->

## Synopsis

**What.** The package `gandr-lang` builds the `gandr` binary. `gandr check <paths>` settles every declaration of every source under the paths given and prints each unsettled one; `gandr test <paths>` runs the same pass and also prints every fixture and every pending source. `gandr check --lint explicit-exits` also reports, as a warning with the edit that settles it, every exit a source leaves to be inferred, which a module otherwise asks for through its `explicit_exits` attribute; `--lint explicit-runs` does the same for every run the checker infers where a computation stands in a position that reads a value, and `--lint explicit-runs=effects` for the runs that perform an effect, which the `explicit_runs` attribute asks for. `gandr check --grant read,write` bounds every capability a declaration holds by the host operations named, refusing one that claims another. `gandr run <file> [arguments…]` checks one source as `check` does and runs it on the L machine: a source declaring `def main() -> -F Integer`, or `def main(args : List(String)) -> -F Integer` to read the arguments, is a program and exits with the integer `main` returns or passes to `Proc.exit`; any other source runs the last name it declares and prints the value. `gandr stage <programs>` builds each staged program its spelling names, checks it end to end — normalization, merge, harvest, readmission and family admission — and prints what the kernel readmitted and how its families were admitted. `gandr fmt <paths>` lays out every source under the paths given through `gandr-surface-format`, writes each source whose layout changes back over it and prints its path; `gandr fmt --check` writes nothing. `gandr ledger syntax --write <directory>` writes the syntax ledger, every rule of the built-in grammar and every attribute of the lowering's registry under the grammar's fingerprint, as `syntax.md` and `syntax.json`, and `gandr ledger exemplars <directory>` verifies one exemplar per committed rule and attribute ([`ledger/README.md`](../../ledger/README.md)). `gandr ledger list [--area <area>] [--status <status>]` prints one line per feature of `ledger/features.sql` and `gandr ledger show <id>` a feature's row, its exemplars' sources whole and its corpus paths: before writing a form, list its area and show each feature it uses. `gandr lsp` serves `gandr-surface-lsp`'s language server on standard input and output until the client sends `exit`: on Unix through the engine hub of the current directory's workspace, which `gandr serve` runs and `gandr lsp` starts when none answers, and in its own process under `--standalone`; `gandr lsp --capabilities` prints what the server advertises. `gandr mcp`, on Unix, serves `gandr-surface-mcp`'s Model Context Protocol server on standard input and output through the same hub, its tools and resources reading the documents the workspace's editors hold open. `gandr view`, on Unix, attaches to the same hub's render bus and follows the document it checked last: full-screen through `gandr-surface-tui`'s side view on a terminal, its reports as plain rows on a pipe. `gandr repl` runs `gandr-surface-repl`'s read-evaluate loop on standard input and output: the line editor on a terminal, a plain transcript when standard input is piped or under `--batch`. `gandr tui` runs the same loop through `gandr-surface-tui`'s terminal face, full-screen, and `gandr tui --smoke` runs that face once off-screen and prints `gandr tui: ready`. A bare `gandr` prints one status line naming the driver version and stating that toolchain management is not implemented. Every verb writes a construct with a glyph (`≃`, `≅`, `⇝`, `∷`) in the spelling `--spelling unicode|ascii` names, else the one `presentation.spelling` names in `$XDG_CONFIG_HOME/gandr/config.toml` (`~/.config` when unset), else Unicode; an editor's `gandr.presentation.spelling` outranks the file for its connection.

**Why.** The driver owns the argument surface and the process boundary, and routes everything after that through `gandr-surface-dispatcher`, which composes the pipeline and decides the gate without a process. The registry name `gandr` belongs to an unrelated crate, so the package is `gandr-lang` and the binary is `gandr`.

**How.** `clap` parses the arguments before anything is written. The invocation is dispatched; the driver hands the walk the dispatcher returns a visitor at the width the invocation asked for, prints each diagnostic the dispatcher's `entries` yields for a source step as `gandr-surface-render-terminal` lays it out, and each fault, then the runner's report and its verdict, through locked handles and fallible `writeln!`, and returns the verdict as its exit code from `main`. `gandr run` runs the dispatcher's `Script` with the operands after the path, writes a value alone to standard output and everything else to standard error, and returns the entry's exit status, or else the run's status, as its exit code. `gandr stage` runs the dispatcher's `Staging` at the width the invocation asked for, prints a line per program, the run's digest and its verdict, and returns the verdict as its exit code. `gandr fmt` steps the dispatcher's `Formatting`, prints the path of each source whose layout changed and each fault, and returns the worst of them as its exit code. `gandr ledger` runs the dispatcher's `LedgerTask`, prints the path of each file written, each exemplar finding and the count verified, or the features asked for, exits one on a finding, and exits two when the ledger cannot be generated, written or read. `gandr lsp` connects to the hub's socket, starting this executable detached as `gandr serve` and retrying for five seconds when nothing answers, hands the standard streams and the connection to `gandr-surface-lsp`'s `relay`, and returns how the session ended as its exit code; under `--standalone` it hands the locked standard streams to `serve` instead. `gandr mcp` reaches the hub the same way and hands the streams and the connection to `gandr-surface-mcp`'s `relay`. `gandr view` reaches the hub the same way, sends the render bus's preface, and hands the connection to `gandr-surface-tui`'s `follow` on a terminal or `follow_plain` otherwise. `gandr serve` binds the socket through `bind` and runs `run_hub` until it lingers out, with `gandr-surface-mcp`'s `serve` as the face for connections speaking lines, its timing lines on standard error. `gandr repl` hands the standard streams to `gandr-surface-repl`'s `run_batch` or `run_interactive` and returns how the loop ended; `gandr tui` checks that standard input and output are a terminal, then hands the terminal to `gandr-surface-tui`'s `run`, or standard output to its `run_smoke` under `--smoke`, and returns how the face ended. Witnesses, each spawning the binary: `tests::cli::a_settled_run_exits_zero`, `tests::cli::an_unsettled_run_exits_one`, `tests::cli::an_unreadable_path_exits_two`, `tests::cli::a_malformed_invocation_exits_two`, `tests::cli::a_grant_bounds_held_capabilities_and_refuses_an_unknown_operation`, `tests::cli::unwritable_standard_output_exits_two`, `tests::cli::goals_report_an_obligation_without_failing`, `tests::cli::the_test_verb_prints_every_fixture_and_pending_source`, `tests::cli::every_width_prints_the_serial_run`, `tests::cli::every_width_stages_the_serial_run`, `tests::cli::fmt_rewrites_what_check_reports`, `tests::cli::the_syntax_ledger_is_written_and_reproduced`, `tests::cli::the_exemplars_verify_and_a_stray_one_is_named`, `tests::cli::the_features_ledger_lists_and_shows_1827`, `tests::cli::help_exits_zero`, `tests::cli::a_bare_invocation_prints_the_status`, `tests::cli::lsp_capabilities_print_one_line_of_json`, `tests::cli::lsp_serves_a_session_over_the_standard_streams`, `tests::cli::lsp_clients_share_one_engine_hub`, `tests::cli::mcp_reads_what_an_editor_holds_open`, `tests::cli::a_view_follows_what_an_editor_holds_open`, `tests::cli::a_piped_repl_session_prints_its_transcript`, `tests::cli::the_tui_smoke_face_prints_ready`, `tests::cli::the_tui_needs_a_terminal`, and for `gandr run` the script-runner rows (§ Where the detail lives).

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
refusals: 0 user absence, 0 unimplemented, 0 malformed source, 0 engine fault
run: settled
seal: sealed
verdict: settled
$ gandr check broken.gandr
error[UnresolvedName]: `missing` is not defined
  ╭▸ broken.gandr:1:14
  │
1 │ def broken = missing ;
  │              ━━━━━━━ not found in this scope
  │
  ╰ note: `broken` is expected to check, and this refusal leaves it unsettled

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
$ gandr stage -j 4 pow:0..8 double:0..8
pow:0..8: 9 of 9 certificates readmitted; 15 families: 2 admitted, 0 partial, 13 plain, 0 refused, 0 over the work bound, 0 faulted
double:0..8: 18 of 18 certificates readmitted; 13 families: 4 admitted, 0 partial, 9 plain, 0 refused, 0 over the work bound, 0 faulted
digest: 64155da969400767
verdict: readmitted
$ printf 'def  answer =  42 ;\n' > answer.gandr
$ gandr fmt --check answer.gandr
answer.gandr
$ echo $?
1
$ gandr fmt answer.gandr
answer.gandr
$ cat answer.gandr
def answer = 42 ;
```

## Where the detail lives

Mechanism, decisions with their alternatives and reversals, and witnesses live in the rustdoc beside the code:

| Topic | Module |
| ----- | ------ |
| Verbs, exit codes, unwritable output, tests and their limits, optional tracing | [`main`](src/main.rs) |
| The user's configuration file | [`config`](src/config.rs) |
| The global allocator | [`allocator`](src/allocator.rs) |

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
