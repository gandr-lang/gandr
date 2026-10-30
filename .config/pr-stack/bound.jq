# What `stack_on_top` does with a top the checked-out branch cannot rebase
# onto because it lacks a trunk change the branch builds on (#3654, #4124,
# #4164). Such a top carries the change only once it merges, or once its
# seat rebases it. A top behind the trunk with its checks pending is the
# normal state of a stack between two landings: its watch queues it once it
# is green, and the queue rebases it. Each such top is a future event, so
# the stacking arms `pr:await` on it and the seat's turn ends (`await.jq`). A
# top conflicting with the trunk past its seat's claim window has no seat
# rebasing it, so the stacking goes past it. A top held or failed needs a
# hand and is refused.
#
# Input: an object with
#   queued  whether the top is in the merge queue or set to enter it;
#   draft   whether the top is a draft, held on purpose (`pr:hold`);
#   merge   the top's `mergeStateStatus`;
#   checks  its head's status check rollup state, or null before any check;
#   age     seconds since its head commit was made, or null.
# Output: `{act, why}`. `act` is `arm` for a top queued, one conflicting
# within the claim window, or one neither held, conflicting nor failed;
# `past` for one conflicting past the window; `refuse` otherwise. `why` says
# what the top waits on or what keeps it out.

include "await" {search: "./"};

($ARGS.named.trunk // "the trunk") as $trunk
| if .queued then {act: "arm", why: "it is queued"}
  elif .draft then {act: "refuse", why: "it is a draft, held"}
  elif .merge == "DIRTY" then
    if (.age // 0) >= window then {act: "past", why: "it has conflicted with \($trunk) past its seat's claim window"}
    else {act: "arm", why: "it conflicts with \($trunk), and its seat rebases it within its claim window"}
    end
  elif .checks == "FAILURE" or .checks == "ERROR" then {act: "refuse", why: "a check on its head failed"}
  else {act: "arm", why: "its checks run or passed, and its watch queues it"}
  end
