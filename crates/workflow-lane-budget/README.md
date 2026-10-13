# gandr-workflow-lane-budget

Each CI lane's median job time over the latest merge-queue and pull-request runs, against the budget the nightly workflow states.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Dependencies](#dependencies)
- [License](#license)

## Synopsis

**What.** `gandr-workflow-lane-budget` installs the `lane-budget` binary. It samples the newest merge-queue and pull-request runs of `ci.yml`, summarises each budgeted job by the lower median of its successful runs, prints a Markdown table of median, budget and standing, and keeps one issue in step: open while any lane is over, closed once every lane is within.

**Why.** CI time drifts one small change at a time: a cache that stops matching, a lane that gains a step, a test that slows. Each change passes review because none is large, and the queue's wall time grows unnoticed. A nightly comparison against budgets written beside the jobs catches the drift within a day and names the lane, without blocking any landing.

**How.** `gh api` lists the runs and each run's jobs; a job's time is its completion less its start. The lower median of a lane's samples is a time some job took, and ignores the slowest half of the window. The budgets are `--budget NAME=SECONDS` arguments in `nightly.yml`, so changing a lane's shape and its budget is one commit. The [crate docs](src/lib.rs) record the alternatives and the reversal.

## Provided features

- `lane-budget --budget NAME=SECONDS...` prints the report; `--runs N` sets the window, ten by default.
- `--issue TITLE` opens, updates, reopens or closes the one issue with exactly that title.
- `BudgetError` names the argument or the `gh` invocation behind every refusal.

## Expected features

`gh` on the path, authenticated for the repository with permission to read Actions and, with `--issue`, to write issues; `GH_REPO` or the checkout names the repository.

## Examples

```sh
mise run ci:lane-budget --budget 'check Clippy wall=300' --budget 'test enforcing targets (linux)=600'
cargo nextest run -p gandr-workflow-lane-budget
```

## Dependencies

`serde` and `serde_json` read `gh`'s issue listing, with the features the root `Cargo.toml` records.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
