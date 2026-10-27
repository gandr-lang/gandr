## The shape

`{{workflow}}` sums {{total}} s over its jobs, past its budget of {{budget}} s, and `{{job}}` is the job that grew. A sweep that cannot fit rotates or samples; no timeout is raised and no test is ignored (`AGENTS.md`, hosted CI budget).

- `{{job}}` rotates, each run taking a fixed share of its work by the run's date, or samples, each run a seeded subset whose seed the log prints; the whole runs across the rotation.
- The workflow's sum returns under {{budget}} s, read from its runs' job timings.
- The regression is the lane budget's own reading of the workflow's next runs.

## Try first

Time `{{job}}`'s parts in its last run's log and split them into shares by cost: the share count whose largest part fits the budget's remainder decides rotation over sampling.

## Sources

- `.github/workflows/{{workflow}}` — primary: the jobs and the budget its header states
- `crates/workflow-lane-budget` — primary: the guard that reads the jobs' timings against the budgets
- `docs/agents/ci-local.md` — secondary: the hosted CI budget and its ceiling

## Readings

| Family | Axis | Selected |
| ------ | ---- | -------- |
| Identity | `univalent` | no — CI scheduling; no construction of the language |
| Locality | `oracle` | no — nothing is replayed |
| Locality | `descent` | yes — a rotated or sampled job covers its whole set across runs; what one run skips and when it owes it is stated |
| Place | `located` | no — one hosted runner class |
| Place | `resident` | no — no representation |
| Dimension | `rewriting` | no — no rule |

## Concerns

| Concern | Touched |
| ------- | ------- |
| `fork` | yes — the job's set is split across runs; the PR says within |
| `oracle` | no |
| `sharing` | no |

## Ledger

None (workflow).

## After

none

## Not in this slice

The other workflows' budgets, and a raised timeout or ceiling, which the budget never takes.
