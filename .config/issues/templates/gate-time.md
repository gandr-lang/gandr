## The shape

`mise run gate:all` on main took {{seconds}} s, past its budget of {{budget}} s. `{{task}}` is its slowest task, and `{{test}}` is its slowest test. The fix splits, samples or speeds up the test that grew. No seat raises the budget to fit a slower gate.

- The task or the test that grew takes less time, or leaves the gate for a lane that needs it.
- `mise run gate:all` on main gives a time under {{budget}} s, and `report:gate-time` prints it within its budget.
- The regression is the report's own reading of the next gate on main.

## Try first

Read the record's `time` of the gate on main (`.config/gate-scope/passed.bash`). Compare the slowest tasks and tests with those of the gate before the time grew. The task or test that grew decides the unit.

## Sources

| Source | Role | What it gives |
| ------ | ---- | ------------- |
| `.config/gate-scope/budget.json` | primary | the budget of the gate on main |
| `.config/gate-scope/times.jq` | primary | the times that the record holds, read from the gate's log |
| `.config/nextest.toml` | secondary | the time bound of each test and CI's profiles |

## Readings

| Family | Axis | Selected |
| ------ | ---- | -------- |
| Identity | `univalent` | no — the time of the local gate; no construction of the language |
| Locality | `oracle` | no — nothing is replayed |
| Locality | `descent` | no — one gate's time, read whole |
| Place | `located` | no — one host |
| Place | `resident` | no — no representation |
| Dimension | `rewriting` | no — no rule |
| Cost | `zero-cost` | no — a time report adds nothing at run time |
| Names | `nominal` | no — a time report binds, allocates and releases no name |
| Level | `general` | no — a time report states no result of the language |

## Concerns

| Concern | Touched |
| ------- | ------- |
| `fork` | no |
| `oracle` | no |
| `sharing` | no |
| `nominal` | no |
| `measure` | no |
| `collapse` | no |

## Engineering

| Row | Bound |
| --- | ----- |
| change | unchanged: none, as a gate whose tasks do not change keeps its time; edit: the fix changes the task or the test that grew, never the whole gate |
| complexity | the gate's time is linear in its tasks and their tests |
| latency | `mise run gate:all` on main takes under {{budget}} s |
| parallelism | the gate's tasks run at once in its slot, and its one full test suite takes the slot's cores |
| memory | n/a — a time report holds no resident state |
| failure | a gate that fails records no time, so the next gate on main reads the budget again |
| streaming | n/a — a gate gives its verdict when its last task ends |

## Ledger

None (workflow).

## After

none

## Not in this slice

A raised budget, which needs its own issue with the reason. The CI lanes' budgets, which the nightly's lane budget holds.
