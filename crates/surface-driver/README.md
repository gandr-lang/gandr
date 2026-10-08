# gandr-lang

The `gandr` binary, the entry point of the gandr language toolchain.

<!-- toc -->

- [Synopsis](#synopsis)
- [Examples](#examples)
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

## License

Apache-2.0 WITH LLVM-exception. The licence text is at the repository root.
