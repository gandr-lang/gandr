# gandr

A programming language built on a small certified kernel. A call-by-push-value core is checked by a defunctionalized machine over a flat, content-addressed term arena; records live in an authenticated, content-defined Merkle search tree.

## Status

`0.0.0`, pre-release. The kernel (universe levels, the term arena and its sharing format, the checking machine and conversion), the core language with normalization by evaluation and its bidirectional checker, the surface parser and its lowering into the core, the expectation language and the language's corpus, the authenticated record plane and the `gandr` driver exist. The driver checks a first fragment of the surface: signatures and definitions over integers, strings and the unit value, thunks, lambdas, returns, forces and applications.

## Usage

```sh
cargo run -p gandr-lang -- check crates/surface-corpus/strict    # every declaration checks, owing nothing
cargo run -p gandr-lang -- check --goals my-sources/              # owed signatures printed as goals
cargo run -p gandr-lang -- test crates/surface-corpus/fixture     # every fixture and pending source printed
```

`gandr check` exits `0` when every declaration settles, `1` when one does not, and `2` on an engine fault, an unreadable path or a malformed invocation. The [driver](crates/surface-driver/README.md) states the verbs and the exit codes; the [corpus](crates/surface-corpus/README.md#the-corpus) states what the two roots hold.

## Crates

`crates/README.md` names every crate, its package and its layer.

## Build

```sh
mise install        # the pinned toolchain and tools
mise run check      # every gate: format, clippy, dylint, rustdoc, specifications, tests, the corpus roots, typos
cargo build-dist    # the shipped binary: fat LTO, size-optimized std
```

`cargo build --release` is the everyday optimized build; `cargo build-dist` (`.cargo/config.toml`) is the whole-program one. `cargo nextest run --workspace` runs the tests; `mise run check:tests-enforcing` runs them again with every specification checked at runtime.

`mise run ci:act` runs the committed Linux CI workflow in a disposable checkout. Each invocation uses distinct container names, so gates can run concurrently across repositories and worktrees. Cached actions run without GitHub fetches; missing actions download on first use.

Completed and interrupted gates remove their containers, networks and volumes. Before starting, each gate reaps resources from abandoned runs whose workflow process is gone; live runs and the shared `act-toolcache` volume remain untouched.

Each gate snapshots the shared action cache. Successful gates publish only new cache entries under a directory lock; a 30-second lock timeout fails the gate.

## Landing changes

Install the hooks with `mise exec -- prek install`. Sign every commit and pass commitlint locally; the ruleset requires signatures on every commit in the pull request range. Run `mise run check` before opening the pull request.

Push the branch to `origin`, open a pull request against `main`, then enable automatic merging:

```sh
git push -u origin <branch>
gh pr create --base main --fill
gh pr merge --merge --auto <n>
```

The merge queue runs the merge-group lanes and lands the change by merge commit. The repository allows only merge commits and deletes the branch after merging.

## License

Apache-2.0 WITH LLVM-exception. See `LICENSE.Apache-2.0.txt` and `LICENSE.LLVM-exception.txt`.
