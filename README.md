# gandr

[![CI](https://github.com/gandr-lang/gandr/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/gandr-lang/gandr/actions/workflows/ci.yml) [![Nightly](https://github.com/gandr-lang/gandr/actions/workflows/nightly.yml/badge.svg?branch=main)](https://github.com/gandr-lang/gandr/actions/workflows/nightly.yml) [![codecov](https://codecov.io/gh/gandr-lang/gandr/graph/badge.svg)](https://codecov.io/gh/gandr-lang/gandr) [![licence](https://img.shields.io/badge/license-Apache--2.0_WITH_LLVM--exception-blue)](LICENSE.Apache-2.0.txt) [![rustc](https://img.shields.io/badge/rustc-nightly--2026--06--25-blue)](rust-toolchain.toml)

A programming language built on a small certified kernel. A call-by-push-value core is checked by a defunctionalized machine over a flat, content-addressed term arena; every declaration a producer hands the kernel is re-checked before admission, and a conversion an untrusted engine decides is replayed from its trace, decision by decision. Values and records live in a content-addressed storage tier: a typed chunk DAG and an authenticated, content-defined Merkle search tree.

## Status

`0.0.0`, pre-release. Every tier exists: the kernel (universe levels, the term arena and sharing format, the checking machine, conversion and its replay, native universe paths, sessions and the stage universe), the core language (normalization by evaluation, the bidirectional checker, incremental checking and the sequent machine), the storage tier's value and record planes, the runtime's native emitter, which runs a program as copy-and-patched machine code, and the surface from grammar and parser through lowering to the driver, the language server, the MCP server and the terminal faces. The corpus lives at the repository's top: its strict root, under `crates/surface-corpus/strict/`, checks owing nothing, and its fixture root, under `corpus/`, states each source's expected verdict.

## Usage

```sh
gandr check crates/surface-corpus/strict      # every declaration checks, owing nothing
gandr check --goals my-sources/               # owed signatures printed as goals
gandr test corpus                          # every fixture and pending source printed
gandr run my-program.gandr                    # check, then run the last declaration and print its value
gandr fmt --check my-sources/                 # list the sources out of layout
```

`gandr check` exits `0` when every declaration settles, `1` when one does not, and `2` on an engine fault, an unreadable path or a malformed invocation.

`gandr lsp` serves the Language Server Protocol over standard input and output; on Unix it reaches the engine hub `gandr serve` runs for the current directory's workspace, starting one when none runs, so every editor on a workspace shares its open documents. [`contrib/gandr-vscode`](contrib/gandr-vscode/README.md) is the Visual Studio Code extension that connects to it. `gandr mcp` serves the Model Context Protocol through the same hub: a model reads the diagnostics, outline and types of the documents the editors hold open. `gandr view` follows the hub's render bus in a terminal beside the editor: every diagnostic of the document checked last, with its derivation, and every hole with its goal.

`gandr repl` and `gandr tui` run the read-evaluate loop, plain and full-screen. The [driver](crates/surface-driver/README.md) states every verb and its exit codes; [`crates/README.md`](crates/README.md) names every crate, its package and its layer.

## Build

```sh
mise install                     # the pinned toolchain and tools
cargo build --release -p gandr-lang
mise run check                   # every gate
```

## License

Apache-2.0 WITH LLVM-exception. See `LICENSE.Apache-2.0.txt` and `LICENSE.LLVM-exception.txt`.
