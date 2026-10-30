# Whether a top the checked-out branch cannot rebase onto is bound for the
# trunk (#3654, #4124), as `stack_on_top` reads it. A top that lacks a trunk
# change the branch builds on carries it only once it merges, so the stacking
# waits for it. A top behind the trunk with its checks pending is the normal
# state of a stack between two landings: its watch queues it once it is
# green, and the queue rebases it. Only a top that cannot land as it stands
# is refused.
#
# Input: an object with
#   queued  whether the top is in the merge queue or set to enter it;
#   draft   whether the top is a draft, held on purpose (`pr:hold`);
#   merge   the top's `mergeStateStatus`;
#   checks  its head's status check rollup state, or null before any check.
# Output: `{act, why}`. `act` is `wait` for a top queued, or one neither held,
# conflicting nor failed; `refuse` otherwise, `why` saying what keeps it out.

if .queued then {act: "wait", why: "it is queued"}
elif .draft then {act: "refuse", why: "it is a draft, held"}
elif .merge == "DIRTY" then {act: "refuse", why: "it conflicts with \($ARGS.named.trunk // "the trunk")"}
elif .checks == "FAILURE" or .checks == "ERROR" then {act: "refuse", why: "a check on its head failed"}
else {act: "wait", why: "its checks run or passed, and its watch queues it"}
end
