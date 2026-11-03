# The line `stall:watch` pages the coordinator with (#4655): a finding's line,
# then the decisions its kind admits, each with the command that carries it
# out (`coordinator.md` § coord-hosts). A hold is a draft with its reason,
# never a page to the seats: their landing tooling re-queues any ready pull
# request that is not a draft. The seat's page is the finding's line alone.
#
#   root-unqueued                queue it, hold it, reassign it
#   ejected, pile-up, red-unrevised
#                                hold it, reassign it
#   conflicting, base-blocked, queued-off-trunk
#                                order the rebase, hold it, reassign it
#   verdict-unfiled              file it, by the command its line names
#   seat-idle                    page the seat to claim, or assign its work
#
# Input: one finding of `detect.jq`, `{kind, number, lane, line, ...}`.
# Output: the coordinator's line, raw.

. as $finding
| "hold it: `mise run pr:hold \($finding.number) \"<what it waits on>\"`" as $hold
| "reassign it" as $reassign
| (if .kind == "root-unqueued" then ["queue it: `gh stack merge`", $hold, $reassign]
   elif (.kind | IN("ejected", "pile-up", "red-unrevised")) then [$hold, $reassign]
   elif (.kind | IN("conflicting", "base-blocked", "queued-off-trunk")) then ["order the rebase", $hold, $reassign]
   elif .kind == "verdict-unfiled" then ["file it: `mise run refactor:file \($finding.number)`"]
   elif .kind == "seat-idle" then ["page the seat to claim", "assign its next work"]
   else error("decide.jq: no decisions for the kind `\(.kind)`")
   end) as $decisions
| "\(.line). Decide: \($decisions | join("; "))"
