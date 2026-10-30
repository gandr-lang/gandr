## The shape

# {{pr}} stands as a `{{kind}}` stall in the `{{lane}}` lane. No seat holds that lane. `stall:watch` pages the coordinator and files this report

- The coordinator routes it. A seat takes the lane, or the coordinator acts on the pull request. It moves it to a held lane, drafts it with its reason (`pr:hold`) or closes it.
- `stall:watch` closes this report itself once no reading finds the stall. Its comment names what clears it: #{{pr}} merges, closes unmerged, or stops its stall.

## Try first

`mise run stall:check` reads the stall again: the `{{kind}}` line on #{{pr}} still stands, or the event is over.

## Sources

| Source | Role | What it gives |
| ------ | ---- | ------------- |
| `#{{pr}}` | primary | the stalled pull request |
| `.config/stall/detect.jq` | primary | the `{{kind}}` finding, its threshold and its line |
| `docs/agents/coordinator.md` | secondary | who routes a lane no seat holds |

## Readings

| Family | Axis | Selected |
| ------ | ---- | -------- |
| Identity | `univalent` | no — a routing event of the landing workflow; no construction of the language |
| Locality | `oracle` | no — nothing is replayed; the detector reads the pull requests and decides |
| Locality | `descent` | no — one pull request's stall, routed whole |
| Place | `located` | no — one repository |
| Place | `resident` | no — no representation |
| Dimension | `rewriting` | no — no rule |
| Cost | `zero-cost` | no — a routing event adds nothing at run time |
| Names | `nominal` | no — a routing event binds, allocates and releases no name |

## Concerns

| Concern | Touched |
| ------- | ------- |
| `fork` | no |
| `oracle` | no |
| `sharing` | no |
| `nominal` | no |

## Ledger

None (workflow).

## After

none

## Not in this slice

The detector's thresholds and lanes, and a seat for the `{{lane}}` lane: both are the coordinator's configuration, never this report's.
