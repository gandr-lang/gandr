## The shape

The table gives each act that ends the stall and its actor.

| Act | Actor |
| --- | ----- |
| takes the `{{lane}}` lane | a seat |
| moves #{{pr}} to a held lane | the coordinator |
| drafts #{{pr}} with its reason (`pr:hold`) | the coordinator |
| closes #{{pr}} | the coordinator |
| closes this report once no reading finds the stall | `stall:watch` |

The closing comment of `stall:watch` names the event that ends the stall: the merge of #{{pr}}, its close unmerged, or the end of its stall.

## Try first

`mise run stall:check` reads the stall again. Its `{{kind}}` line on #{{pr}} shows that the stall stands.

## Sources

| Source | Role | What it gives |
| ------ | ---- | ------------- |
| `#{{pr}}` | primary | the stalled pull request |
| `.config/stall/detect.jq` | primary | the `{{kind}}` finding, its threshold and its line |
| `docs/agents/coordinator.md` | secondary | the seat that routes a lane with no seat |

## Readings

| Family | Axis | Selected |
| ------ | ---- | -------- |
| Identity | `univalent` | no — a routing event of the landing workflow, with no construction of the language |
| Locality | `oracle` | no — nothing is replayed. The detector reads the pull requests and decides |
| Locality | `descent` | no — the stall of one pull request, routed whole |
| Place | `located` | no — one repository |
| Place | `resident` | no — no representation |
| Dimension | `rewriting` | no — no rule |
| Cost | `zero-cost` | no — a routing event adds nothing at run time |
| Names | `nominal` | no — a routing event binds, allocates and releases no name |
| Level | `general` | no — a routing event states no result of the language |

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
| change | n/a — a routing event, with no change to a code path |
| complexity | n/a — the detector reads one pull request whole |
| latency | n/a — the coordinator routes the stall, and no tool path changes |
| parallelism | n/a — one report for each stall |
| memory | n/a — no change to a code path |
| failure | `stall:watch` reads the stall again on its next run, so a lost page comes again |
| streaming | n/a — one page for each stall, sent whole |

## Ledger

None (workflow).

## After

none

## Not in this slice

The thresholds and lanes of the detector, and a seat for the `{{lane}}` lane. Both are the configuration of the coordinator, never of this report.
