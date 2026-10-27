## The shape

# {{pr}} stands as a `{{kind}}` stall in the `{{lane}}` lane, and no seat holds that lane, so `stall:watch` paged the coordinator and filed this report

- The coordinator routes it: a seat takes the lane, the pull request is relabelled to a held lane, drafted with its reason (`pr:hold`) or closed.
- `stall:watch` closes this report itself once no reading finds the stall. Its comment names what cleared it: #{{pr}} merged, closed unmerged, or no longer stalled.

## Try first

`mise run stall:check` reads the stall again: the `{{kind}}` line on #{{pr}} still stands, or the event is over.

## Sources

- `#{{pr}}` — primary: the stalled pull request
- `.config/stall/detect.jq` — primary: the `{{kind}}` finding, its threshold and its line
- `docs/agents/coordinator.md` — secondary: who routes a lane no seat holds

## Readings

| Family | Axis | Selected |
| ------ | ---- | -------- |
| Identity | `univalent` | no — a routing event of the landing workflow; no construction of the language |
| Locality | `oracle` | no — nothing is replayed; the detector reads the pull requests and decides |
| Locality | `descent` | no — one pull request's stall, routed whole |
| Place | `located` | no — one repository |
| Place | `resident` | no — no representation |
| Dimension | `rewriting` | no — no rule |

## Concerns

| Concern | Touched |
| ------- | ------- |
| `fork` | no |
| `oracle` | no |
| `sharing` | no |

## Ledger

None (workflow).

## After

none

## Not in this slice

The detector's thresholds and lanes, and a seat for the `{{lane}}` lane: both are the coordinator's configuration, never this report's.
