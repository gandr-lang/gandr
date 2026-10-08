# gandr

A programming language built on a small certified kernel. A call-by-push-value core is checked by a defunctionalized machine over a flat, content-addressed term arena; records live in an authenticated, content-defined Merkle search tree.

## Status

`0.0.0`, pre-release. The kernel (universe levels, the term arena and its sharing format, the checking machine and conversion), the core language with normalization by evaluation, the concrete syntax tree, the authenticated record plane and the `gandr` driver stub exist. The driver parses its arguments and reports its version; nothing else is wired to it yet.

## Crates

`crates/README.md` names every crate, its package and its layer.

## Build

```sh
mise install        # the pinned toolchain and tools
mise run check      # every gate: format, clippy, dylint, rustdoc, specifications, tests, typos
cargo build-dist    # the shipped binary: fat LTO, size-optimized std
```

`cargo build --release` is the everyday optimized build; `cargo build-dist` (`.cargo/config.toml`) is the whole-program one. `cargo nextest run --workspace` runs the tests; `mise run check:tests-enforcing` runs them again with every specification checked at runtime.

`mise run ci:act` runs the committed Linux CI workflow in a disposable checkout. Each invocation uses distinct container names, so gates can run concurrently across repositories and worktrees. Cached actions run without GitHub fetches; missing actions download on first use.

Each gate snapshots the shared action cache. Successful gates publish only new cache entries under a directory lock; a 30-second lock timeout fails the gate.

## License

Apache-2.0 WITH LLVM-exception. See `LICENSE.Apache-2.0.txt` and `LICENSE.LLVM-exception.txt`.
