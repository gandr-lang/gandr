# gandr-lang

Driver for the [gandr](https://github.com/gandr-lang/gandr) language toolchain.

Installs the `gandr` binary. The driver manages the gandr toolchain: it fetches toolchain releases, installs optional components (script runner, REPL, LSP, native compile host), and dispatches to installed tools.

## Status

Pre-release stub. The CLI parses arguments and reports its version; toolchain management is under active development in the
[gandr repository](https://github.com/gandr-lang/gandr).

## License

Apache-2.0 WITH LLVM-exception.
