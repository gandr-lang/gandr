## The shape

`{{workflow}}` sums {{total}} s over its jobs, past its budget of {{budget}} s. `{{job}}` is the job whose time rises. A sweep that cannot fit rotates or samples. No seat raises a timeout or ignores a test (`AGENTS.md`, hosted CI budget).

- `{{job}}` rotates or samples. A rotating run takes a fixed share of the work by the run's date. A sampling run takes a seeded subset. Its log prints the seed. The rotation covers the whole set across runs.
- The job timings of its runs show the workflow's sum under {{budget}} s.
- The regression is the lane budget's own reading of the workflow's next runs.

## Try first

Time the parts of `{{job}}` in its last run's log. Split them into shares by cost. The share count whose largest part fits the budget's remainder decides between rotation and sampling.

## Sources

| Source | Role | What it gives |
| ------ | ---- | ------------- |
| `.github/workflows/{{workflow}}` | primary | the jobs and the budget its header states |
| `crates/workflow-lane-budget` | primary | the guard that reads the jobs' timings against the budgets |
| `docs/agents/ci-local.md` | secondary | the hosted CI budget and its ceiling |

## Readings

| Family | Axis | Selected |
| ------ | ---- | -------- |
| Identity | `univalent` | no — CI scheduling; no construction of the language |
| Locality | `oracle` | no — nothing is replayed |
| Locality | `descent` | yes — a rotated or sampled job covers its whole set across runs; what one run skips and when it owes it is stated |
| Place | `located` | no — one hosted runner class |
| Place | `resident` | no — no representation |
| Dimension | `rewriting` | no — no rule |
| Cost | `zero-cost` | no — a budget report adds nothing at run time |
| Names | `nominal` | no — a budget report binds, allocates and releases no name |

## Concerns

| Concern | Touched |
| ------- | ------- |
| `fork` | yes — the job's set is split across runs; the PR says within |
| `oracle` | no |
| `sharing` | no |
| `nominal` | no |

## Ledger

None (workflow).

## After

none

## Not in this slice

The other workflows' budgets, and a raised timeout or ceiling, which the budget never takes.
