# gandr-workflow-hotpath-guard

A commit's hotpath checks, filed on one issue per regressed function.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Dependencies](#dependencies)
- [License](#license)

## Synopsis

**What.** `gandr-workflow-hotpath-guard` installs the `hotpath-guard` binary. It reads a commit's `hotpath / <benchmark>` checks and the pull request the commit heads, and prints a Markdown report of every failed check: its run, its wall-time line, and each site over its policy's threshold with the before/after numbers. Each regressed function has one issue, titled `perf: <function>` and labelled `kind:performance` with the function's area. Its body is the index of the function's regressions: one row per pull request and benchmark, with the commit, the metric, the delta, the status and links to the run and the report. Each new regression's report is a comment on that issue. The body also carries the `## Lint` obligation once per function: the fix states whether a quenchant dylint could have refused the pattern that regressed.

**Why.** The hotpath check is not required: hotpath Cloud posts it after the benchmark upload, which can arrive after the rest of the pipeline, and no pull request waits for it. A red check nobody reads lands with the pull request. The guard turns each failure into a row the triage lane can route, while the pull request is still open or after it merged. Keying by function rather than by pull request keeps one function's regressions together, so they can be claimed as a set.

**How.** The hotpath guard workflow runs on every completed hotpath check that failed or passed. `gh api` lists the commit's check runs and the pull requests GitHub associates with it, and the guard names the one whose head is the commit. Rows change as follows:

- A failed check records a row for each function it names. A rerun of the same pull request and benchmark rewrites that row without a new comment, unless the set of regressed functions changed.
- A passing check marks the pull request's open row in that benchmark `fixed`.
- A timing failure in which the wall time and every regressed function moved up together (within 8 points, call counts unchanged, no allocation check failed) is marked `runner shift`. It gets no comment, and its row proposes the policy's false-positive step to the owner.
- `accepted` is read but never written by the guard; the verdict obligation records it.

The issue closes when no row is open and reopens on the next open row. The guard rewrites only the table's rows, so prose and hand-folded rows in the same columns stay as written. The [crate docs](src/lib.rs) record the decisions, the alternatives and the reversal.

## Provided features

- `hotpath-guard --sha SHA` prints the report; `--repository OWNER/NAME` defaults to `GITHUB_REPOSITORY`.
- `--file-issue` records the run on each regressed function's issue (opened when it has none), marks the pull request's rows of passing benchmarks fixed, and closes or reopens each issue as its rows stand. A commit with no concluded hotpath check touches no issue.
- `GuardError` names the argument or the `gh` invocation behind every refusal; a refusal exits 2.

## Expected features

`gh` on the path, authenticated for the repository with permission to read checks and pull requests and, with `--file-issue`, to write issues, and `GH_REPO` or the checkout naming the repository.

## Examples

```sh
mise run ci:hotpath-guard --repository gandr-lang/gandr --sha 914a768fb32501be92e5cb4d28ce6613dfa01022
cargo nextest run -p gandr-workflow-hotpath-guard
```

## Dependencies

`serde` and `serde_json` read `gh`'s answers, with the features the root `Cargo.toml` records.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
