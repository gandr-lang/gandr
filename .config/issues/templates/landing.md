## The shape

The lane that the claim names repairs `{{check}}` on `landing`, never with a revert. The repair lands through the queue as any other unit. The next green head of `landing` ends the defect.

| Act | Actor |
| --- | ----- |
| repairs `{{check}}` on `landing` | the seat of the claim's lane |
| moves the claim to another lane | the coordinator |
| comments a newer red head of `{{check}}` | `landing:watch` |

## Try first

`mise run {{check}}` on `{{head}}` fails, and on the parent of `{{culprit}}` it passes. The failing lines above name the fault.

## Sources

| Source | Role | What it gives |
| ------ | ---- | ------------- |
| `#{{pr}}` | primary | the pull request that brings `{{culprit}}`, or `none` when GitHub names none |
| `.config/integration/search.jq` | primary | the search over the first parents that names `{{culprit}}` |
| `.config/integration/owner.jq` | primary | the lane, the title and the `FIX` page |
| `#6587` | secondary | the head watcher of `landing` |

## Readings

| Family | Axis | Selected |
| ------ | ---- | -------- |
| Identity | `univalent` | no — a red check of the workflow, with no construction of the language |
| Locality | `oracle` | no — the watcher runs the check and trusts no earlier answer |
| Locality | `descent` | yes — the search narrows the red head to one commit on the first parents |
| Place | `located` | no — one repository |
| Place | `resident` | no — no representation |
| Dimension | `rewriting` | no — no rule |
| Cost | `zero-cost` | no — a red check adds nothing at run time |
| Names | `nominal` | no — a red check binds, allocates and releases no name |
| Level | `general` | no — a red check states no result of the language |

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
| change | n/a — the repair states its own bounds on its pull request |
| complexity | n/a — the repair states its own bounds on its pull request |
| latency | n/a — the repair states its own bounds on its pull request |
| parallelism | n/a — one defect for each red check |
| memory | n/a — the repair states its own bounds on its pull request |
| failure | `landing:watch` reads the head again on its next move, so a lost page comes again |

## Ledger

None (workflow).

## After

none

## Not in this slice

A fault that the gate of `pr:open` does not select. The integration cycle's known-red list of #5469 holds it.
