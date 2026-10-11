# gandr-workflow-spec-cost

Executable specifications ranked by the time the slowest enforcing tests spend checking them.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [How a sample is charged](#how-a-sample-is-charged)
- [The profiled build](#the-profiled-build)
- [Dependencies](#dependencies)
- [License](#license)

## Synopsis

**What.** `gandr-workflow-spec-cost` installs the `spec-cost` binary. It profiles named tests, or the slowest enforcing tests the test-timing store names, under `perf`. It charges every sample to the `#[spec]` check on its stack and prints each test's share of checking, then the checks ranked by charged time.

**Why.** Enforcement runs every clause on every call, so a clause that traverses state grown across calls makes the enforced code quadratic, and the enforcing lane is CI's critical path. Clause shapes do not show which checks the tests pay for; a census of them ranks a cheap clause on a hot path below an expensive one nobody calls. A profile of the tests that set the lane's wall time does show it.

**How.** `cargo nextest list` builds the tests' packages with enforcement, frame pointers and line tables into `target/spec-cost`. Each test runs once, single-threaded, under `perf record --call-graph fp`. `perf script --inline` reads back every sample's frames with their source lines. `syn` reads the line span of every `#[spec]` attribute in `crates/`. A frame whose line falls inside one is that specification's check.

## Provided features

- `spec-cost` prints a table of the profiled tests (seconds sampled, share in checks), then the checks by charged time: seconds, share of all samples, innermost seconds, how many tests reached the check, and the attribute's file, line and item.
- `--tests N` profiles the N slowest enforcing tests of the newest `--runs` stored runs, 5 and 5 by default; `--test "BINARY TEST"`, repeatable, profiles named tests instead, written as nextest prints them.
- `--frequency HZ` sets the sampling rate, 499 by default; `--top N` the number of checks listed, 30 by default.
- `Regions`, `Stacks`, `charge` and `Ledger` are the library behind the binary; `CostError` names the file, command or test behind every refusal.

## Expected features

Linux with `perf` on the path and `perf_event_paranoid` at 2 or lower, which allows sampling one's own processes. `cargo nextest` on the path. The timing store comes from `mise run ci:timing` unless every test is named.

Tests run one at a time in a single process each, so a test that leans on parallelism is profiled at its sequential cost. Ignored tests cannot be named.

## Examples

```sh
mise run ci:timing                          # fill the store
mise run ci:spec-cost                       # the five slowest enforcing tests
mise run ci:spec-cost --tests 3 --top 10
cargo run --locked -p gandr-workflow-spec-cost -- --test "gandr-surface-parser::tests acceptance::corpus_parses_totally"
cargo nextest run -p gandr-workflow-spec-cost
RUSTFLAGS="--cfg anodized_panic" CARGO_TARGET_DIR=target/enforcing cargo nextest run -p gandr-workflow-spec-cost
```

## How a sample is charged

anodized expands each clause with the clause's own spans, so the machine code of a check carries the attribute's lines. A sample whose stack holds such a frame was spent checking.

The function body runs inside a closure passed to `anodized::__::eval_once`, also spanned by the attribute. A frame called from `eval_once` is therefore the body, not a check, and is skipped.

A check can call code with checks of its own. The sample is charged once, to the outermost check on the stack, the one whose removal would remove the time. The innermost check is reported beside it as the time that check itself was running. A check with little charged time and much innermost time is cheap itself but reached through another check's clause.

Shares are of all samples across the profiled tests, so the checks' column sums to the overall share in checks. The alternative was charging every check on the stack, which counts nested time more than once and stops the column from summing.

## The profiled build

`RUSTFLAGS="--cfg anodized_panic -C force-frame-pointers=yes"` and `CARGO_PROFILE_TEST_DEBUG=line-tables-only` into `target/spec-cost`. Frame pointers make `perf`'s unwinding cheap and exact. DWARF unwinding copies stack snapshots per sample and loses deep stacks, and specification checks sit deep. Line tables give each inlined frame its source line. The separate target directory keeps the enforcing gate's build state untouched, at the cost of one more workspace build.

## Dependencies

`syn` reads the attribute spans; `proc-macro2` with `span-locations` gives them line numbers. Both are already in the build graph through the proc-macros, with default features off. `syn` was chosen over `ra_ap_syntax`, which tracks rust-analyzer's release cadence and API churn, and over `tree-sitter-rust`, which needs a C build and a separate grammar crate. The root `Cargo.toml` records each enabled feature. The test-timing store is read through `gandr-workflow-test-timing`.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
