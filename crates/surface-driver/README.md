# gandr-lang

The `gandr` binary, the entry point of the gandr language toolchain: `gandr check` and `gandr test` over gandr sources, with the run's verdict as the exit code.

<!-- toc -->

- [Synopsis](#synopsis)
- [Verbs](#verbs)
- [Exit codes](#exit-codes)
- [Examples](#examples)
- [Output the driver cannot write is a fault](#output-the-driver-cannot-write-is-a-fault)
- [Optional tracing](#optional-tracing)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** The package `gandr-lang` builds the `gandr` binary. `gandr check <paths>` settles every declaration of every source under the paths given and prints each unsettled one; `gandr test <paths>` runs the same pass and also prints every fixture and every pending source. A bare `gandr` prints one status line naming the driver version and stating that toolchain management is not implemented.

**Why.** The driver owns the argument surface and the process boundary, and routes everything after that through `gandr-surface-dispatcher`, which composes the pipeline and decides the gate without a process. The registry name `gandr` belongs to an unrelated crate, so the package is `gandr-lang` and the binary is `gandr`.

**How.** `clap` parses the arguments before anything is written. The invocation is dispatched; the driver advances the walk the dispatcher returns, prints each source's lines and each fault, then the runner's report and its verdict, through locked handles and fallible `writeln!`, and returns the verdict as its exit code from `main`. Witnesses, each spawning the binary: `cli::cli::a_settled_run_exits_zero`, `cli::cli::an_unsettled_run_exits_one`, `cli::cli::an_unreadable_path_exits_two`, `cli::cli::a_malformed_invocation_exits_two`, `cli::cli::unwritable_standard_output_exits_two`, `cli::cli::goals_report_an_obligation_without_failing`, `cli::cli::the_test_verb_prints_every_fixture_and_pending_source`, `cli::cli::help_exits_zero`, `cli::cli::a_bare_invocation_prints_the_status`.

## Verbs

| Invocation | Prints | Fails on |
| ---------- | ------ | -------- |
| `gandr check <paths>` | each unsettled declaration, each source refused as a whole | any unsettled declaration |
| `gandr check --goals <paths>` | as `check`, a declaration unsettled by its obligations alone marked `goal:` | any unsettled declaration but those |
| `gandr test <paths>` | as `check`, plus every fixture, settled or not, and every pending source's refusal | as `check` |

A path is a source file of any name, or a directory searched for `.gandr` sources. The directories a source sits in decide its root — `strict`, `fixture`, or `fixture/pending` — and a source under none is strict ([membership is location](../surface-dispatcher/README.md#membership-is-location)). Each source line is `<path>: <report>`; each fault is `gandr: <path>: <fault>` on standard error. Every run closes standard output with the runner's report — the sources read by root, the lowerings, the goals, the exercised table, the ledger size, the declaration and fixture counts, the surviving obligations, the refusals by class, the run's settlement and its seal — and `verdict: settled`, `unsettled` or `faulted`.

## Exit codes

| Code | Meaning |
| ---- | ------- |
| `0` | every declaration settled; also `--help`, `--version` and a bare `gandr` |
| `1` | at least one declaration is unsettled, or a source was not read as its root expects |
| `2` | an engine fault, an unreadable path or one naming no source, a malformed invocation, or output the driver could not write |

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
broken.gandr: unsettled `broken` at 0..22: states checks owing 0; produced refuses UnresolvedName (malformed source)
…
verdict: unsettled
$ echo $?
1
```

## Output the driver cannot write is a fault

`main` returns its exit code rather than a `Result`, so a write or flush that fails — a closed pipe, a full disk — is noted on standard error, when that is writable, and exits `2`, the code every fault shares. The runtime ignores `SIGPIPE`, so a reader that closed early surfaces as a failed write, not a signal. The alternative was returning the I/O error from `main`, whose runtime path exits `1` and would read as an unsettled run. The choice reverses if a fault class needs its own code, which would be a fourth row above.

## Optional tracing

Build with `cargo build -p gandr-lang --features tracing` to report driver and dispatcher diagnostics on stderr. The feature forwards to `gandr-surface-dispatcher`; this driver has no evaluator dependency and does not activate evaluator tracing. A default build carries no tracing instrumentation or dependency: `cargo tree -p gandr-lang -e normal,build` lists neither `tracing` nor `tracing-subscriber` until the feature is on.

Argument parsing runs before subscriber installation, so help, version and argument errors retain their ordinary output. A scoped, thread-local subscriber reports dispatch-span completion and successful output flushing, then restores the prior subscriber when the invocation ends. Libraries install no subscriber. Standard-output write and flush errors remain faults rather than successful-completion events.

The output backend is [`tracing-subscriber`](https://docs.rs/tracing-subscriber/0.3.23/tracing_subscriber/fmt/index.html) 0.3.23 with only `fmt` and its required registry/std support. ANSI formatting, the log bridge, filter parsing, JSON and time integrations stay off. This release includes the [ANSI-input escaping fix](https://rustsec.org/advisories/RUSTSEC-2025-0055); the current events contain fixed messages and no user payloads. A global subscriber was rejected because the invocation need not own process-wide diagnostics; an environment filter adds parsing machinery for no current CLI option. Revisit those choices when the driver gains a consumer requiring them, or the selected version needs a security or maintenance replacement.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
