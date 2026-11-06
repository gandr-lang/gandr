## The shape

The table gives the reading of `{{function}}` on `main` at `{{commit}}`.

| Function | Count | Budget | Policy |
| -------- | ----- | ------ | ------ |
| `{{function}}` | {{count}} | {{budget}} | `{{policy}}` |

The hotpath check fails on `main`. Each pull request against `main` repeats the breach. The reason of the policy reads: {{reason}}.

The landing that moves the count past the budget decides the fix. The table gives each case and its fix.

| Case | Fix |
| ---- | --- |
| the count grows where the reason of the policy forbids it | a fix at the site of that landing brings the count back under the budget |
| the count grows with the series, and the reason still holds | the budget rises, and the comment of the policy states the new count and the reason for the rise |

The regression is the hotpath check itself: the report of `main` passes the budget.

## Try first

Bisect the hotpath reports of the series over `main`, from the last passing report to `{{commit}}`. Run `hotpath:report` at each step. The bisection ends at the landing that moves `{{function}}` past {{budget}}. That landing decides the fix.

## Sources

| Source | Role | What it gives |
| ------ | ---- | ------------- |
| `{{policy}}` | primary | the budget and the reason it states |
| `crates/workflow-hotpath-guard` | primary | the guard that reads the report against the policy |
| `docs/agents/ci-local.md` | secondary | the place of the hotpath check among the checks |

## Readings

| Family | Axis | Selected |
| ------ | ---- | -------- |
| Identity | `univalent` | no — a measurement against a budget, with no construction of the language |
| Locality | `oracle` | no — the count is measured, not replayed |
| Locality | `descent` | {{descent}} |
| Place | `located` | no — one benchmark on one host class |
| Place | `resident` | no — no representation changes |
| Dimension | `rewriting` | no — no rule |
| Cost | `zero-cost` | no — the time of the toolchain against a budget, with nothing added to a gandr artifact at run time |
| Names | `nominal` | no — a timing report binds, allocates and releases no name |

## Concerns

| Concern | Touched |
| ------- | ------- |
| `fork` | no |
| `oracle` | no |
| `sharing` | {{sharing}} |
| `nominal` | no |
| `measure` | no |
| `collapse` | no |

## Engineering

| Row | Bound |
| --- | ----- |
| change | n/a — a budget breach on `main`. The fix states its own incremental path |
| complexity | the count of `{{function}}` on the inputs of the series, at most {{budget}} |
| latency | `{{function}}` at or under {{budget}} on `main` |
| parallelism | n/a — the budget reads the count of one function on one host class |
| memory | the pull request of the fix states the allocations for each call before and after |
| failure | n/a — a measurement. A crash loses one report. The next run measures again |

## Ledger

None: a budget the ledger does not carry.

## After

none

## Not in this slice

The budgets of other functions, and the reading of the policy by the guard.
