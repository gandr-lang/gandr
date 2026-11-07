# The line `stall:watch` pages the coordinator with (#4655): a finding's line,
# then the decisions its kind admits, each with the command that carries it
# out (`coordinator.md` § coord-hosts). A hold is a draft with its reason,
# never a page to the seats: their landing tooling re-queues any ready pull
# request that is not a draft. The seat's page is the finding's line alone.
#
#   root-unqueued                queue it, hold it, reassign it
#   ejected, red-unrevised       hold it, reassign it
#   pile-up                      hold it, which cuts it to the top of its
#                                stack; once the stack watcher cuts it, its
#                                seat's `pr:open` after its fix; reassign it
#   conflicting, base-blocked, queued-off-trunk
#                                order the rebase, hold it, reassign it
#   verdict-unfiled              file it, by the command its line names
#   seat-idle                    the seat's last reported line, then: when the
#                                claim command gives work, no decision, as the
#                                seat's page names that command; else assign
#                                its next work (#5996)
#
# A pile-up's root is open when the page is sent, as `detect.jq` reads open
# pull requests alone. The stack watcher may cut it before the decision
# runs, and closes it unmerged so. `pr:hold` then refuses it, as a hold would
# reopen it and stop the stack above it again (#5902).
#
# Input: one finding of `detect.jq`, `{kind, number, lane, line, ...}`; a
# `seat-idle` finding also carries `last`, the seat's last reported line or
# null, and `work`, the line the claim command's dry run printed or null,
# which `stall:watch` sets.
# Output: the coordinator's line, raw.

. as $finding
| "hold it: `mise run pr:hold \($finding.number) \"<what it waits on>\"`" as $hold
| "reassign it" as $reassign
| (if .kind == "root-unqueued" then ["queue it: `gh stack merge`", $hold, $reassign]
   elif (.kind | IN("ejected", "red-unrevised")) then [$hold, $reassign]
   elif .kind == "pile-up" then
     ["\($hold), which cuts it to the top of its stack", "once the stack watcher cuts it, its seat fixes it and runs `mise run pr:open`", $reassign]
   elif (.kind | IN("conflicting", "base-blocked", "queued-off-trunk")) then ["order the rebase", $hold, $reassign]
   elif .kind == "verdict-unfiled" then ["file it: `mise run refactor:file \($finding.number)`"]
   elif .kind == "seat-idle" then (if .work == null then ["assign its next work, as the claim gives none"] else [] end)
   else error("decide.jq: no decisions for the kind `\(.kind)`")
   end) as $decisions
| (if .kind == "seat-idle" then "\(.line). Its last line: \(if .last == null then "none" else .last | @json end)" + (if .work == null then "" else "; the claim gives \(.work)" end) else .line end) as $said
| if $decisions == [] then $said else "\($said). Decide: \($decisions | join("; "))" end
