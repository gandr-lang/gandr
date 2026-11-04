# Whether `pr:open` on a branch takes the stack top's hold (#5122,
# `hold.bash`'s `top_hold_take`). One `pr:open` at a time holds the top from
# its stacking to its push, so no other one restacks under its gate.
#
# Input: an object with
#   hold  the hold the server keeps, `{holder, head, began, deadline}`, the
#         times in epoch seconds, or null;
#   own   the checked-out branch;
#   now   the time, in epoch seconds.
# Output: one of
#   {act: "take"}                  no hold stands, so the branch takes it;
#   {act: "take", over: <holder>}  the hold is past its deadline, so its
#                                  holder crashed or left it, and the branch
#                                  takes it over;
#   {act: "renew", began: <time>}  the branch holds it already: an earlier run
#                                  stacked it and stopped for a gate, so its
#                                  deadline moves and its start stays;
#   {act: "wait", why: <line>}     another branch holds it.
if .hold == null then {act: "take"}
elif .hold.holder == .own then {act: "renew", began: .hold.began}
elif .hold.deadline <= .now then {act: "take", over: .hold.holder}
else {act: "wait", why: "the stack top is held by `\(.hold.holder)` at \(.hold.head[:12]) since \(.hold.began | todate), until \(.hold.deadline | todate) at the latest"}
end
