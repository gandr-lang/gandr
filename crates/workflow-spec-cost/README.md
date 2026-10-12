# gandr-workflow-spec-cost

Executable specifications ranked by the time the slowest enforcing tests spend checking them, and each test's enforcing time over its plain time.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [How a sample is charged](#how-a-sample-is-charged)
- [The profiled build](#the-profiled-build)
- [The enforcing/plain ratio](#the-enforcingplain-ratio)
- [Dependencies](#dependencies)
- [License](#license)

## Synopsis

**What.** `gandr-workflow-spec-cost` installs the `spec-cost` binary. It profiles named tests, or the slowest enforcing tests the test-timing store names, under `perf`. It charges every sample to the `#[spec]` check on its stack and prints each test's share of checking, then the checks ranked by charged time. It also installs `spec-cost-ratio`, which divides each test's time in an enforcing nextest JUnit report by its time in a plain one and flags the tests whose checks dominate them; CI reports it on every enforcing run.

**Why.** Enforcement runs every clause on every call, so a clause that traverses state grown across calls makes the enforced code quadratic, and the enforcing lane is CI's critical path. Clause shapes do not show which checks the tests pay for; a census of them ranks a cheap clause on a hot path below an expensive one nobody calls. A profile of the tests that set the lane's wall time does show it.

**How.** `cargo nextest list` builds the tests' packages with enforcement, frame pointers and line tables into `target/spec-cost`. Each test runs once, single-threaded, under `perf record --call-graph fp`. `perf script --inline` reads back every sample's frames with their source lines. `syn` reads the line span of every `#[spec]` attribute in `crates/`. A frame whose line falls inside one is that specification's check.

## Provided features

- `spec-cost` prints a table of the profiled tests (seconds sampled, share in checks), then the checks by charged time: seconds, share of all samples, innermost seconds, how many tests reached the check, and the attribute's file, line and item.
- `--tests N` profiles the N slowest enforcing tests of the newest `--runs` stored runs, 5 and 5 by default; `--test "BINARY TEST"`, repeatable, profiles named tests instead, written as nextest prints them.
- `--frequency HZ` sets the sampling rate, 499 by default; `--top N` the number of checks listed, 30 by default.
- `Regions`, `Stacks`, `charge` and `Ledger` are the library behind the binary; `CostError` names the file, command or test behind every refusal.
- `spec-cost-ratio --plain REPORT --enforcing REPORT --baseline-commit SHA --baseline-age-hours H` prints Markdown: the baseline, then the tests taking at least `--floor` seconds enforcing (0.25 by default) by descending ratio, every one at or above `--threshold` (4 by default) flagged, as many as `--top` (20 by default) or as are flagged, then the totals. `pair` and `Comparisons` are the library behind it.

## Expected features

Linux with `perf` on the path and `perf_event_paranoid` at 2 or lower, which allows sampling one's own processes. `cargo nextest` on the path. The timing store comes from `mise run ci:timing` unless every test is named.

Tests run one at a time in a single process each, so a test that leans on parallelism is profiled at its sequential cost. Ignored tests cannot be named.

`spec-cost-ratio` reads any two nextest JUnit reports; it needs neither `perf` nor the store.

## Examples

```sh
mise run ci:timing                          # fill the store
mise run ci:spec-cost                       # the five slowest enforcing tests
mise run ci:spec-cost --tests 3 --top 10
cargo run --locked -p gandr-workflow-spec-cost -- --test "gandr-surface-parser::tests acceptance::corpus_parses_totally"
cargo nextest run -p gandr-workflow-spec-cost
RUSTFLAGS="--cfg anodized_panic" CARGO_TARGET_DIR=target/enforcing cargo nextest run -p gandr-workflow-spec-cost
gh run download RUN -n junit-cargo-test-plain-baseline -D target/plain-baseline
mise run ci:spec-cost-ratio --plain target/plain-baseline/ci/junit.xml \
  --enforcing target/nextest/ci-enforcing/junit.xml --baseline-commit SHA --baseline-age-hours 0
```

## How a sample is charged

anodized expands each clause with the clause's own spans, so the machine code of a check carries the attribute's lines. A sample whose stack holds such a frame was spent checking.

The function body runs inside a closure passed to `anodized::__::eval_once`, also spanned by the attribute. A frame called from `eval_once` is therefore the body, not a check, and is skipped.

A check can call code with checks of its own. The sample is charged once, to the outermost check on the stack, the one whose removal would remove the time. The innermost check is reported beside it as the time that check itself was running. A check with little charged time and much innermost time is cheap itself but reached through another check's clause.

Shares are of all samples across the profiled tests, so the checks' column sums to the overall share in checks. The alternative was charging every check on the stack, which counts nested time more than once and stops the column from summing.

## The profiled build

`RUSTFLAGS="--cfg anodized_panic -C force-frame-pointers=yes"` and `CARGO_PROFILE_TEST_DEBUG=line-tables-only` into `target/spec-cost`. Frame pointers make `perf`'s unwinding cheap and exact. DWARF unwinding copies stack snapshots per sample and loses deep stacks, and specification checks sit deep. Line tables give each inlined frame its source line. The separate target directory keeps the enforcing gate's build state untouched, at the cost of one more workspace build.

## The enforcing/plain ratio

A test's ratio is the factor its checks multiply its time by. The daily scheduled run of `main`, and any dispatch with `plain-baseline` set, times every workspace test without enforcement in the `cargo-test-plain-baseline` lane and publishes its report. That lane only reads cached build state: a full plain build saved beside the queue's would evict it. Every Linux enforcing lane downloads the newest baseline of `main`, runs `mise run ci:spec-cost-ratio`, writes the result as its job summary with the baseline's commit and age, and uploads it as the `spec-cost-ratio` artifact. The step never fails the lane: it measures and gates nothing.

The threshold, 4, comes from the profiled ranking: the tests whose checks walk accumulated state spend three quarters or more of their time in checks, the rest about half. The `ratio` module documents the choice, the floor and the reversal.

## Dependencies

`syn` reads the attribute spans; `proc-macro2` with `span-locations` gives them line numbers. Both are already in the build graph through the proc-macros, with default features off. `syn` was chosen over `ra_ap_syntax`, which tracks rust-analyzer's release cadence and API churn, and over `tree-sitter-rust`, which needs a C build and a separate grammar crate. The root `Cargo.toml` records each enabled feature. The test-timing store is read through `gandr-workflow-test-timing`.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
