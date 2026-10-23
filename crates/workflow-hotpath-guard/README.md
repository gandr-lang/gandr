# gandr-workflow-hotpath-guard

A commit's hotpath checks, filed on one issue per regressed function.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Dependencies](#dependencies)
- [License](#license)

## Synopsis

**What.** `gandr-workflow-hotpath-guard` installs the `hotpath-guard` binary. It reads a commit's `hotpath / <benchmark>` checks and their pull request, and prints a Markdown report of every failed check: its run, its wall-time line, and each site over its policy's threshold with the before/after numbers. Each regressed function has one issue, titled `perf: <function>` and labelled `kind:performance` with the function's area. Its body is the index of the function's regressions: one row per pull request and benchmark, with the commit, the metric, the delta, the status and links to the run and the report. Each pull request's report is one comment on that issue, marked `<!-- hotpath: pr=<n> -->` and edited by every later run of that pull request. The body also carries the `## Lint` obligation once per function: the fix states whether a quenchant dylint could have refused the pattern that regressed.

**Why.** The hotpath check is not required: hotpath Cloud posts it after the benchmark upload, which can arrive after the rest of the pipeline, and no pull request waits for it. A red check nobody reads lands with the pull request. The guard turns each failure into a row the triage lane can route, while the pull request is still open or after it merged. Keying by function rather than by pull request keeps one function's regressions together, so they can be claimed as a set.

**How.** The hotpath guard workflow runs on every completed hotpath check that failed or passed, one pull request's runs at a time. The pull request is the one the check run event names (`--pull`), so a restack that force-pushes the branch before the guard runs still files under it; without one, `gh api` lists the pull requests GitHub associates with the commit, and the guard names the one whose head is the commit. Rows and comments change as follows:

- A failed check records a row for each function it names. The pull request's comment on that issue is edited to the run's report, or posted when it has none; a rerun or a restack rewrites the row and edits the comment, and never adds one.
- A passing check marks the pull request's open row in that benchmark `fixed` and edits its comment to say no check failed.
- A timing failure in which the wall time and every regressed function moved up together (within 8 points, call counts unchanged, no allocation check failed) is marked `runner shift`. It posts no comment, only edits the pull request's existing one, and its row proposes the policy's false-positive step to the owner.
- A failed check whose pull request's body carries a settled `hotpath: accepted — <benchmark> …` verdict for its benchmark writes the row `accepted`. It posts no comment, only edits the pull request's existing one, and a function with no issue gets none opened. For a failed check without that verdict, the report names the missing verdict.

A pull request that adds a bench workload lands it alone, before the change it measures. A report compares each row with its base's run, so a workload the base never ran reads its whole first run as a regression.

The issue closes when no row is open and reopens on the next open row. The guard rewrites only the table's rows, so prose and hand-folded rows in the same columns stay as written. The [crate docs](src/lib.rs) record the decisions, the alternatives and the reversal.

## Provided features

- `hotpath-guard --sha SHA` prints the report; `--repository OWNER/NAME` defaults to `GITHUB_REPOSITORY`; `--pull N` names the pull request instead of looking it up from the commit.
- `--file-issue` records the run on each regressed function's issue (opened when it has none), edits or posts the pull request's one report comment there, marks the pull request's rows of passing benchmarks fixed, and closes or reopens each issue as its rows stand. A commit with no concluded hotpath check touches no issue.
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
