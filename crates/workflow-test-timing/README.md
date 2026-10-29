# gandr-workflow-test-timing

nextest priority levels proposed from the per-test durations of recent merge-queue runs.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Levels and margins](#levels-and-margins)
- [The lane a test is timed in](#the-lane-a-test-is-timed-in)
- [The store](#the-store)
- [Dependencies](#dependencies)
- [License](#license)

## Synopsis

**What.** `gandr-workflow-test-timing` installs the `test-timing` binary. It reads the JUnit reports of the latest successful merge-queue runs, summarises each test, compares a proposed priority level with the one `.config/nextest.toml` sets now, and prints the overrides that would set the proposed levels.

**Why.** nextest starts higher-priority tests first, so a suite whose slowest tests start early finishes sooner on a fixed number of threads. Which tests are slowest changes with the code, and a hand-kept list goes stale. Every CI test lane already uploads a JUnit report with per-test times; this crate turns those reports into a proposal a reviewer accepts in a commit.

**How.** `gh run list` names the latest successful merge-queue runs of `ci.yml`, and `gh run download` stores each run's `junit-*` artifacts once. Each test is summarised by the lower median of its samples in the lane where that median is greatest. A level table with a margin either side of each boundary turns the median and the current priority into a proposal. The current priority is the first `[[profile.default.overrides]]` table whose filter matches the test, as nextest applies it.

## Provided features

- `test-timing` prints the run identifiers, a table of every test that has or would have a priority, and the proposed overrides.
- `--runs N` reads the newest N stored runs, 5 by default. `--offline` reads the store without invoking `gh`.
- `Overrides::parse` reads the priority overrides whose filters are unions of `test(=NAME)` and `test(TEXT)` terms, and refuses any other filter by name.
- `TimingError` names the file, command or configuration term behind every refusal.

## Expected features

`gh` on the path, authenticated for the repository, unless `--offline`. Runs older than the artifacts' retention cannot be fetched.

## Examples

```sh
mise run ci:timing              # fetch, then report on the latest five runs
mise run ci:timing --runs 10    # a longer window
cargo nextest run -p gandr-workflow-test-timing
RUSTFLAGS="--cfg anodized_panic" CARGO_TARGET_DIR=target/enforcing cargo nextest run -p gandr-workflow-test-timing
```

A reviewer reads the table, replaces the priority-setting overrides in `.config/nextest.toml` with the accepted part of the generated tables, and commits the change with the report's run identifiers.

## Levels and margins

| Priority | Boundary | Enters at or above | Leaves below |
| -------: | -------: | -----------------: | -----------: |
| 100 | 120 s | 150 s | 96 s |
| 90 | 60 s | 75 s | 48 s |
| 80 | 30 s | 37.5 s | 24 s |
| 70 | 15 s | 18.75 s | 12 s |

A test below a level enters it when its median reaches the boundary plus a quarter; a test at or above a level stays in it until its median falls below the boundary less a fifth. A median that wanders across a boundary between windows therefore leaves the level unchanged. A test proposed for no level runs at nextest's default of 0.

The summary is the lower median, the sample at position ⌊(n − 1) / 2⌋ in ascending order: a time a run actually took, and over five runs it ignores the two slowest. A row whose slowest and fastest samples differ by more than half the median is marked `unsteady`, and its level is the reviewer's decision.

The alternative was timing-balanced partitions generated from the same data; nextest's own partitioning is count- and hash-based, so balancing by time would mean generating filter expressions per shard. The priorities serve one runner; the choice reverses when the suite is sharded across runners.

## The lane a test is timed in

A test's priority applies in every lane, so it is chosen by the lane where the test takes longest: the enforcing lanes, where executable specifications run, are the critical path. A test name shared by two binaries takes the slower binary's summary, because nextest's `test()` filter matches the name in every binary.

## The store

Runs are stored under `target/test-timing`, one directory per run identifier. A download lands in a scratch directory and is renamed into place when complete, so an interrupted fetch leaves nothing a later report reads, and a stored run is never fetched again.

## Dependencies

`gandr-workflow-github` runs every `gh` invocation and names the one that failed. Its `read` runs the run listing and each download again past a transient server error. `roxmltree` reads the reports: a read-only tree with no unsafe code and no published advisory, chosen over `quick-xml`, which carries two advisories from 2026. `toml` reads the nextest configuration. Both keep their default features off; the root `Cargo.toml` records each enabled feature and its reason.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
