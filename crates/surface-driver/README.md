# gandr-lang

The `gandr` binary, the entry point of the gandr language toolchain.

<!-- toc -->

- [Synopsis](#synopsis)
- [Examples](#examples)
- [Optional tracing](#optional-tracing)
- [License](#license)

<!-- tocstop -->

## Synopsis

**What.** The package `gandr-lang` builds the `gandr` binary. It accepts `--help` and `--version` and no other argument; a bare `gandr` prints one status line naming the driver version and stating that toolchain management is not implemented.

**Why.** The driver owns the argument surface and the process boundary, and routes everything after that through `gandr-surface-dispatcher`, which a test exercises without a process. The registry name `gandr` belongs to an unrelated crate, so the package is `gandr-lang` and the binary is `gandr`.

**How.** `clap` parses the arguments before anything is written, so `--help`, `--version` and an argument error take clap's exit path. A bare invocation dispatches `Invocation::Status`, writes the report through a locked standard-output handle with a fallible `writeln!`, and flushes it; a closed or full standard output is an error exit rather than a panic.

## Examples

```console
$ cargo run -q -p gandr-lang
gandr 0.0.0 — toolchain management is not yet implemented; see https://github.com/gandr-lang/gandr
$ cargo run -q -p gandr-lang -- --version
gandr 0.0.0
```

## Optional tracing

Build with `cargo build -p gandr-lang --features tracing` to report driver and dispatcher diagnostics on stderr. The feature forwards to `gandr-surface-dispatcher`; this driver has no evaluator dependency and does not activate evaluator tracing. Default builds contain no tracing instrumentation or dependency.

Default-build measurement on aarch64-apple-darwin, using the release profile before and after adding the optional feature: the normal/build dependency graph is unchanged, the executable remains 952,432 bytes, and its machine-code section remains 416,164 bytes. The measured default executable and code-size deltas are both zero; this is a build-size measurement, not a runtime benchmark.

Argument parsing runs before subscriber installation, so help, version and argument errors retain their ordinary output. A scoped, thread-local subscriber reports dispatch-span completion and successful status-output flushing, then restores the prior subscriber when the invocation ends. Libraries install no subscriber. Standard-output write and flush errors remain errors rather than successful-completion events.

The output backend is [`tracing-subscriber`](https://docs.rs/tracing-subscriber/0.3.23/tracing_subscriber/fmt/index.html) 0.3.23 with only `fmt` and its required registry/std support. ANSI formatting, the log bridge, filter parsing, JSON and time integrations stay off. This release includes the [ANSI-input escaping fix](https://rustsec.org/advisories/RUSTSEC-2025-0055); the current events contain fixed messages and no user payloads. A global subscriber was rejected because the invocation need not own process-wide diagnostics; an environment filter adds parsing machinery for no current CLI option. Revisit those choices when the driver gains a consumer requiring them, or the selected version needs a security or maintenance replacement.

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
