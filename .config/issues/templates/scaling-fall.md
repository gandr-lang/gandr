## The shape

The scaling account reads a fall at `{{head}}`. The speed-up of `gandr check` at {{threads}} threads on NUMA nodes {{nodes}} is {{now}}×, and it was {{before}}× at `{{previous}}`. The fall is {{drop}} %, past the account's share of {{share}} %. The fix finds the landing between the two heads that adds a serial step or a contended lock, and widens it again.

- The fix names the landing that flattens the curve, with the step that it serialises.
- The fix gives back the speed-up of `{{previous}}` at {{threads}} threads, within the account's share.
- The regression is the account's own row of the head after the fix.

## Try first

Measure the curve again at `{{head}}` and at `{{previous}}` on the wide host, with no mutation run. A fall that does not repeat is noise, and the issue closes with both curves. For a fall that repeats, bisect the heads between them.

## Sources

| Source | Role | What it gives |
| ------ | ---- | ------------- |
| `whole-system-parallelism.md` | primary | the levels of one check, and the width that each level leaves |
| `parallelism-area-map.md` | secondary | the driver holds the one pool, and `-j` sets its width |

## Readings

| Family | Axis | Selected |
| ------ | ---- | -------- |
| Identity | `univalent` | no — the width of a run; no construction of the language |
| Locality | `oracle` | no — nothing is replayed |
| Locality | `descent` | yes — the serial step that the fall adds is the part of the cover that no longer runs at once |
| Place | `located` | no — one host |
| Place | `resident` | no — no representation |
| Dimension | `rewriting` | no — no rule |
| Cost | `zero-cost` | no — the fix adds nothing at run time |
| Names | `nominal` | no — the fix binds, allocates and releases no name |
| Level | `general` | no — a width states no result of the language |

## Concerns

| Concern | Touched |
| ------- | ------- |
| `fork` | yes — the fall is a loss of width on the driver's one pool |
| `oracle` | no |
| `sharing` | no |
| `nominal` | no |
| `measure` | no |
| `collapse` | no |

## Engineering

| Row | Bound |
| --- | ----- |
| change | unchanged: none, as the fix keeps the work of each step; edit: the fix changes the step that the fall serialises |
| streaming | n/a — the fix changes when steps run, and each check's results come as before |
| complexity | the check's work is as before, and its span falls back to that of `{{previous}}` |
| latency | the check at {{threads}} threads takes the wall time of `{{previous}}` again, within the account's share |
| parallelism | the speed-up at {{threads}} threads is {{before}}× or more again, and the account's next row shows it |
| memory | n/a — the fix changes when steps run, not what they hold |
| failure | n/a — the fix changes when steps run, and a run that fails fails as before |

## Ledger

None (workflow).

## After

none

## Not in this slice

A curve wider than the wide host, which another host would need.
