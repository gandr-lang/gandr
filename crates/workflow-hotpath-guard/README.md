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

- A failed check records a row for each function it names, except a timing function within its run's global shift (below). The pull request's comment on that issue is edited to the run's report, or posted when it has none; a rerun or a restack rewrites the row and edits the comment, and never adds one.
- A passing check marks the pull request's open row in that benchmark `fixed` and edits its comment to say no check failed.
- A timing failure is judged against its run's global shift: the median move of every function both full timing reports time, the head's and the base's the summary names, as their runs kept them (the `hotpath-<commit>` artifact). A function files only when its move beside the shift, `(1 + d) / (1 + s) − 1`, crosses the policy's threshold. A failure in which none does, while the wall time and the shift both do, is marked `runner shift`, stating the shift and the function count; it posts no comment, only edits the pull request's existing one. Allocation failures are judged apart. Without both reports, or with fewer than 10 functions in common, every function files as the check names it.
- A failed check whose pull request's body carries a settled `hotpath: accepted — <benchmark> …` verdict for its benchmark writes the row `accepted`. It posts no comment, only edits the pull request's existing one, and a function with no issue gets none opened. For a failed check without that verdict, the report names the missing verdict.

A pull request that adds a bench workload lands it alone, before the change it measures. A report compares each row with its base's run, so a workload the base never ran reads its whole first run as a regression.

The issue closes when no row is open and reopens on the next open row. The table is collapsed under a summary counting its rows and the open ones; the guard rewrites only the rows and that summary, so prose and hand-folded rows in the same columns stay as written. The [crate docs](src/lib.rs) record the decisions, the alternatives and the reversal.

## Provided features

- `hotpath-guard --sha SHA` prints the report; `--repository OWNER/NAME` defaults to `GITHUB_REPOSITORY`; `--pull N` names the pull request instead of looking it up from the commit; `--policies DIR` names the directory of `<benchmark>-policy.toml` files the global shift is judged under, `hotpath` by default.
- `--file-issue` records the run on each regressed function's issue (opened when it has none), edits or posts the pull request's one report comment there, marks the pull request's rows of passing benchmarks fixed, and closes or reopens each issue as its rows stand. A commit with no concluded hotpath check touches no issue.
- `GuardError` names the argument or the `gh` invocation behind every refusal; a refusal exits 2.
- `hotpath-judge` judges a commit's runs of one benchmark against its base's, several a side, under the benchmark's policy, and writes a `hotpath / <benchmark>` check run's body in hotpath Cloud's summary shape, which the guard files like the Cloud's own. hotpath Cloud never judges a function under the policy's `min_percent_total` share of the run; the judge does, down to 0.1 %, flagging such a row only when its median moved past the threshold and every run of the commit lies past every run of the base. `--band` judges only those rows, as CI does on a pull request; without it every row is judged, as CI does on main's push against the commit main stood at before it, which hotpath Cloud does not judge (`mise run ci:hotpath-judge`). The [module docs](src/judge.rs) record the decision.

## Expected features

`gh` on the path, authenticated for the repository with permission to read checks, pull requests and Actions artifacts and, with `--file-issue`, to write issues, and `GH_REPO` or the checkout naming the repository. `--sha` names the commit in full, as its kept reports are named.

## Examples

```sh
mise run ci:hotpath-guard --repository gandr-lang/gandr --sha 914a768fb32501be92e5cb4d28ce6613dfa01022
cargo run -p gandr-workflow-hotpath-guard --bin hotpath-judge -- --repository gandr-lang/gandr \
  --head 17756fc17 --base 8d13f30c8 --benchmark store-timing-band --policy hotpath/store-timing-policy.toml \
  --band --base-run base-1.json --head-run head-1.json --output check.json
cargo nextest run -p gandr-workflow-hotpath-guard
```

## Dependencies

`gandr-workflow-github` runs every `gh` invocation and names the one that failed. Its `read` runs each read-only invocation again past a transient server error; a write runs once. `serde` and `serde_json` read `gh`'s answers and the hotpath reports; `toml` reads the regression policy the judge applies; each with the features the root `Cargo.toml` records.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
