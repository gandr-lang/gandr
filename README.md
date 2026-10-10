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

CI builds every target under `profile.test`, which inherits size-optimized `release` without debuginfo and explicitly keeps debug assertions and overflow checks. `NEXTEST_PROFILE=ci mise run check:tests` uses that build; `NEXTEST_PROFILE=ci mise run check:tests-enforcing` keeps its checked artifacts in `target/enforcing`. The corpus uses the same Cargo profile. `release` and the aggressive, uncached `dist` profile remain separate.

Build-state archives contain the test artifacts from both target directories, compressed with zstd and uploaded without recompression. Complete archives are cached separately from Cargo dependencies so integration-test binaries survive cache cleanup. Cargo validates source checksums rather than checkout timestamps. Main promotes queue artifacts into shared caches; hosted manual test runs warm branch-local caches. Mise caches installed tools by locked pins, including sizelint, so warm CI installs reuse binaries.

`mise run ci:act` runs the committed Linux CI workflow in a disposable checkout. Two host-wide slots bound concurrent gates across repositories and worktrees; further invocations wait until a slot frees. Dead holders are reclaimed. Each invocation uses distinct container names. Cached actions run without GitHub fetches; missing actions download on first use.

Completed and interrupted gates remove their containers, networks and volumes. Before starting, each gate reaps resources from abandoned runs whose workflow process is gone; live runs and the shared `act-toolcache` volume remain untouched.

Each gate snapshots the shared action cache. Successful gates publish only new cache entries under a directory lock; a 30-second lock timeout fails the gate.

## Landing changes

Install the hooks with `mise exec -- prek install`. Run `mise run check`, then sign the commit and pass commitlint locally; the ruleset requires signatures on every commit in the pull request range. For changes to `.github/` (including `.github/docker/`) or `.config/mise/tasks/`, also run `mise run ci:act` after committing. Other changes use the native gates and the hosted merge queue.

Push the branch, open a pull request, then wait for its landing:

```sh
git push -u origin <branch>
gh pr create --base main --fill
mise run pr:land
```

`pr:land [<n>]` defaults to the current branch's pull request. It enables auto-merge and watches both the pull request and its queue entry every 30 seconds, printing state changes.

| Outcome | Exit | Output |
| ------- | ---- | ------ |
| Merged | `0` | Merge commit, merge-group run URL and each job's wall time |
| Failed checks or dequeue | `1` | Failing run's logs |
| 90-minute timeout | `2` | Last observed state |
| `UNMERGEABLE` queue entry | `3` | Entries ahead and shared files |

For an `UNMERGEABLE` entry, rebase onto `main` after the entries ahead merge, then run the task again.

The merge queue runs the merge-group lanes and lands the change by merge commit. The repository allows only merge commits and deletes the branch after merging.

## License

Apache-2.0 WITH LLVM-exception. See `LICENSE.Apache-2.0.txt` and `LICENSE.LLVM-exception.txt`.
