# What `stack_on_top` does with a top the checked-out branch cannot rebase
# onto because it lacks a trunk change the branch builds on (#3654, #4124,
# #4164). Such a top carries the change only once it merges. Only a top that
# can merge, with no hold, reaches this program (`joins.jq`, #7188). A top
# queued, or one whose checks run or passed, is a future event, so the
# stacking arms `pr:await` on it and the seat's turn ends (`await.jq`). A top
# whose check failed needs a hand and is refused.
#
# Input: an object with
#   queued  whether the top is in the merge queue or set to enter it;
#   checks  its head's status check rollup state, or null before any check.
# Output: `{act, why}`. `act` is `arm` or `refuse`, and `why` says what the
# top waits on or what keeps it out.

if .queued then {act: "arm", why: "it is queued"}
elif .checks == "FAILURE" or .checks == "ERROR" then {act: "refuse", why: "a check on its head failed"}
else {act: "arm", why: "its checks run or passed, and its watch queues it"}
end
