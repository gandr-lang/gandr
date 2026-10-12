# gandr

A programming language built on a small certified kernel. A call-by-push-value core is checked by a defunctionalized machine over a flat, content-addressed term arena; records live in an authenticated, content-defined Merkle search tree.

## Status

`0.0.0`, pre-release. The kernel (universe levels, the term arena and its sharing format, the checking machine and conversion), the core language with normalization by evaluation and its bidirectional checker, the surface parser and its lowering into the core, the expectation language and the language's corpus, the authenticated record plane and the `gandr` driver exist. The driver checks a first fragment of the surface: signatures and definitions over integers, strings and the unit value, thunks, lambdas, returns, forces and applications.

## Usage

```sh
cargo run -p gandr-lang -- check crates/surface-corpus/strict    # every declaration checks, owing nothing
cargo run -p gandr-lang -- check --goals my-sources/              # owed signatures printed as goals
cargo run -p gandr-lang -- test crates/surface-corpus/fixture     # every fixture and pending source printed
cargo run -p gandr-lang -- check --jobs 1 crates/surface-corpus/strict   # one source at a time; the default uses every performance core
```

`gandr check` exits `0` when every declaration settles, `1` when one does not, and `2` on an engine fault, an unreadable path or a malformed invocation. The [driver](crates/surface-driver/README.md) states the verbs and the exit codes; the [corpus](crates/surface-corpus/README.md#the-corpus) states what the two roots hold.

`gandr lsp` serves the Language Server Protocol over standard input and output; on Unix it reaches the engine hub `gandr serve` runs for the current directory's workspace, starting one when none runs, so every editor on a workspace shares its open documents. [`contrib/gandr-vscode`](contrib/gandr-vscode/README.md) is the Visual Studio Code extension that connects to it.

`gandr mcp` serves the Model Context Protocol over standard input and output through the same hub: a model reads the diagnostics, outline and types of the documents the workspace's editors hold open, at the version the editor shows.

`gandr view` follows the same hub's render bus in a terminal beside the editor: every diagnostic of the document checked last, at its row and column with its derivation, and every hole with its goal, refreshed at each check.

## Crates

`crates/README.md` names every crate, its package and its layer.

## Build

```sh
mise install        # the pinned toolchain and tools
mise run check      # every gate: format, clippy, dylint, rustdoc, specifications, tests, the corpus roots, typos
cargo build-dist    # the shipped binary: fat LTO, size-optimized std
```

`cargo build --release` is the everyday optimized build; `cargo build-dist` (`.cargo/config.toml`) is the whole-program one. `cargo nextest run --workspace` runs the tests; `mise run check:tests-enforcing` runs them again with every specification checked at runtime.

The Clippy wall runs in both plain and enforcing modes locally and in CI. `mise run check:clippy-enforcing` covers cfg-gated runtime sentinels under the enforcing test profile in `target/enforcing`. Clippy writes check metadata rather than build artifacts, so the CI lane restores only the shared crate downloads. The plain pass stays whole because the plain expansion turns each predicate into `(true || predicate)`, code the enforcing pass never lints; in CI it is also the plain graph's compile check over every target.

Dylint runs plain in both modes. Its separately built plugin does not inherit workspace features; the task strips the panic and print enforcement cfgs while preserving the policy flags. The lints read source, and quenchant's gates check the plugin's own specifications.

CI builds every target under `profile.test`, which inherits size-optimized `release` without debuginfo and explicitly keeps debug assertions and overflow checks. `NEXTEST_PROFILE=ci-enforcing mise run check:tests-enforcing` keeps its checked artifacts in `target/enforcing` and its report separate; `NEXTEST_PROFILE=ci mise run check:tests-plain-only` runs the plain delta under the same Cargo profile. The `ci-enforcing` profile kills a test after ten minutes rather than four, at least twice the slowest enforcing test. The corpus uses the same Cargo profile. `release` and the aggressive, uncached `dist` profile remain separate.

Nextest starts the measured heavy tail first in both its default and CI profiles. JUnit reports retain individual test durations for both plain and enforcing runs, and `mise run ci:timing` reads them from the latest successful queue runs to propose each test's priority level; the levels in `.config/nextest.toml` are its reviewed output. Generated tests share immutable grammar and rewrite-rule fixtures within each test process. Session fixtures borrow the shared `common::GRAMMAR` directly; `common::grammar()` returns an owned clone for session constructors and lowering adapters. Membership checks borrow each immutable table view once, retaining the complete mold census and first-invalid-id checks. Test domains, case counts, assertions and timeout budgets remain unchanged.

Executable specifications dominate the enforcing lane's time. `mise run ci:spec-cost` profiles the slowest enforcing tests the timing store names under `perf` (Linux only). It ranks the `#[spec]` checks by the time charged to them, the outermost check on each sampled stack, so the costly clauses are found by measurement rather than by reading.

In CI the enforcing run is the full test pass, on Linux and macOS. Enforcement adds checks and runtime sentinels but removes one test, the wall-clock latency budget in `gandr-surface-parser`, which is gated `cfg(not(anodized_panic))` because predicates would run inside the timed parse. The Linux plain lane builds and runs only that test, then the corpus roots and private-item rustdoc; a new plain-only test joins the filters of `build:tests-plain-only` and `check:tests-plain-only`. Locally, `mise run check` still runs both full suites. Each lane owns a zstd archive of its test-profile target directory, uploaded without recompression and cached separately from Cargo dependencies so integration-test binaries survive cache cleanup. The required workspace gate names aggregate their platform's lanes and fail if any fails, skips or is cancelled.

Cargo validates source checksums rather than checkout timestamps. Successful compilation remains cacheable when a later test fails, without changing that failure's verdict. A test lane restores the newest state built under the same toolchain pin, whatever its manifests, and Cargo's fingerprints rebuild what changed: a manifest edit to one crate leaves third-party dependencies compiled, and a Git dependency at another revision builds under a different metadata hash, so it never reads as fresh. A cache miss may restore a completed queue run's artifacts of the same toolchain pin, including a failed test run: unlike branch-local caches, these are readable from a new queue ref. A toolchain bump starts every lane from scratch and discards the superseded artifacts a pin accumulates. Main promotes exact-commit queue artifacts into shared caches; hosted manual runs and queue retries also warm branch-local caches. The shared dependency, toolchain and tool caches have one writer per platform: the plain lane on Linux and the enforcing lane on macOS.

The enforcing Linux test lane resolves adequacy witnesses after its build, so witness discovery lists binaries that already exist instead of compiling the enforcing graph a second time. The policy lane builds no test graph. Its exact-key cache contains both the Dylint library and the installed specification-gate binary, which the enforcing lane restores from the same key; toolchain, policy and dependency pins invalidate them together. Dylint, invocation-state, enforcing-configuration and witness checks still run on every run. Mise caches installed tools by locked pins, including sizelint, so warm CI installs reuse binaries.

Archive creation stops the job if either tar or zstd fails.

The workspace names the pinned `quenchant-anodized` facade `anodized`, with defaults disabled and its `anodized` feature enabled to compile the development backend. The backend is the [anodized fork](https://github.com/gandr-lang/anodized), supporting ordinary and const functions and type refinements without `std` or the `logic` feature. `--cfg anodized_panic` selects enforcement for the whole build graph, including const evaluation and `anodized::types::Spec::predicate`. Without an instrumentation cfg, predicates remain type-checked but are not evaluated; pre-state captures retain the backend's ordinary evaluation semantics. With the feature disabled, strip mode erases specifications and excludes the backend entirely. The feature alone never enables enforcement.

Import `anodized::spec` and write `#[spec(...)]`; the policy lane denies qualified specification attributes. Direct use of the fork lacks the facade's backend-free strip mode; handwritten assertions lack its shared specification representation. Reconsider the facade when the specification backend or its supported build modes change.

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
