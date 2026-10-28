## The shape

`{{function}}` measures {{count}} against its budget of {{budget}} on `main` at `{{commit}}`, so the hotpath check fails on `main` and every pull request against it repeats the breach. The budget is in `{{policy}}`, whose reason reads: {{reason}}.

- Find the landing that moved the count past the budget.
- Then one of two, decided by that landing:
  - the count grew where the policy's reason forbids it: the fix is at that landing's site, and the count returns under the budget;
  - the count grew with the series and the reason still holds: the budget rises, with the policy's comment updated to the new count and the reason for the rise.
- The regression is the hotpath check itself: `main`'s report passes the budget.

## Try first

Bisect the series' hotpath reports over `main` from the last passing report to `{{commit}}`, running `hotpath:report` at each step, to the landing that moved `{{function}}` past {{budget}}. The landing decides which of the two fixes applies.

## Sources

| Source | Role | What it gives |
| ------ | ---- | ------------- |
| `{{policy}}` | primary | the budget and the reason it states |
| `crates/workflow-hotpath-guard` | primary | the guard that reads the report against the policy |
| `docs/agents/ci-local.md` | secondary | the hotpath check's place among the checks |

## Readings

| Family | Axis | Selected |
| ------ | ---- | -------- |
| Identity | `univalent` | no — a measurement against a budget; no construction of the language |
| Locality | `oracle` | no — the count is measured, not replayed |
| Locality | `descent` | {{descent}} |
| Place | `located` | no — one benchmark on one host class |
| Place | `resident` | no — no representation changes |
| Dimension | `rewriting` | no — no rule |
| Cost | `zero-cost` | no — the toolchain's own time against a budget; nothing is added to a gandr artifact at run time |

## Concerns

| Concern | Touched |
| ------- | ------- |
| `fork` | no |
| `oracle` | no |
| `sharing` | {{sharing}} |

## Ledger

None: a budget the ledger does not carry.

## After

none

## Not in this slice

Budgets other than `{{function}}`'s, and the guard's reading of the policy.
