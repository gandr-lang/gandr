# gandr-workflow-lane-budget

Each CI lane's median job time over the latest merge-queue and pull-request runs, against the budget the nightly workflow states.

- [Synopsis](#synopsis)
- [Provided features](#provided-features)
- [Expected features](#expected-features)
- [Examples](#examples)
- [Dependencies](#dependencies)
- [License](#license)

## Synopsis

**What.** `gandr-workflow-lane-budget` installs the `lane-budget` binary. It samples the newest merge-queue and pull-request runs of `ci.yml`, classifies each by the cone its landing touched — deep when it changed a file under `crates/kernel-*` or `crates/core-*`, `Cargo.lock`, `rust-toolchain.toml` or `.cargo/`, surface otherwise — summarises each budgeted job by the lower median of its successful runs per cone, prints a Markdown table of class, median, budget and standing, and keeps one issue in step: open while any lane is over, closed once every lane is within.

**Why.** CI time drifts one small change at a time: a cache that stops matching, a lane that gains a step, a test that slows. Each change passes review because none is large, and the queue's wall time grows unnoticed. A nightly comparison against budgets written beside the jobs catches the drift within a day and names the lane, without blocking any landing. A landing that touches the kernel or core stack rebuilds the whole enforcing graph and takes longer than one that touches only the surface, so the enforcing lanes are held by cone: one budget is tight enough to miss a surface regression and loose enough to excuse a deep one.

**How.** `gh api` lists the runs and each run's jobs; a job's time is its completion less its start. Each run's head is compared against its merge base — the queue's branch names the entry's base — and the changed files name its cone. The lower median of a lane's samples in a cone is a time some job took, and ignores the slowest half of the window. The budgets are `--budget NAME=SECONDS` arguments in `nightly.yml`, with `NAME:deep=SECONDS` naming a cone's budget, so changing a lane's shape and its budget is one commit. A lane only the daily scheduled run of `ci.yml` holds is a `--daily NAME=SECONDS` budget, sampled over the newest scheduled runs in a table of its own; a lane of `nightly.yml` is a `--nightly NAME=SECONDS` budget, sampled over that workflow's scheduled runs. A workflow's hosted budget is a `--summed NAME=BUDGET/CEILING` argument: every active workflow's newest completed runs are timed whole, wall time and the sum of their completed jobs' times, in a last table with the Actions cache's usage, and the named workflow is held to its budget by the median sum and to its ceiling by every run. The [crate docs](src/lib.rs) state the nightly report, the two cones, the daily window, the summed budget and the one issue.

## Provided features

- `lane-budget --budget NAME=SECONDS...` prints the report; `NAME:deep=SECONDS` names the deep budget of a cone-classified lane; `--daily NAME=SECONDS` holds a lane of the daily scheduled run over the scheduled runs; `--nightly NAME=SECONDS` holds a lane of the nightly workflow over its scheduled runs; `--summed NAME=BUDGET/CEILING` holds a workflow's summed job time per run and adds the table of every workflow's run times, naming the job that grew in each run past the ceiling; `--runs N` sets each window, ten by default.
- `--issue TITLE` opens, updates, reopens or closes the one issue with exactly that title.
- A `--summed` workflow whose newest completed run passed its ceiling makes the command exit 2 after its report and its filing (#3013), so a night past the ceiling turns the next run red.
- `BudgetError` names the argument or the `gh` invocation behind every refusal.

## Expected features

`gh` on the path, authenticated for the repository with permission to read Actions and, with `--issue`, to write issues; `GH_REPO` or the checkout names the repository.

## Examples

```sh
mise run ci:lane-budget --budget 'check Clippy wall=300' --budget 'test enforcing targets (linux)=600'
cargo nextest run -p gandr-workflow-lane-budget
```

## Dependencies

`gandr-workflow-github` runs every `gh` invocation and names the one that failed. `serde` and `serde_json` read `gh`'s issue listing, with the features the root `Cargo.toml` records.

## License

Apache-2.0 WITH LLVM-exception. See [Apache-2.0](../../LICENSE.Apache-2.0.txt) and the [LLVM exception](../../LICENSE.LLVM-exception.txt) at the repository root.
