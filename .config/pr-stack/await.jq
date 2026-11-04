# What `pr:open` waits on rather than refuses (#4164), and when `pr:await`
# wakes the seat. An answer that names a future event is a wait: the seat
# arms `pr:await` as a deferred job, ends its turn, and runs `pr:open` again
# when the job exits.

# A seat's claim window in seconds (`units.md`): a top conflicting with the
# trunk whose head stood this long is stacked past.
def window: 14400;

# The line a seat's harness arms `pr:await <n>` on, as `pr:land` arms
# `pr:watch`.
def arm($n): "arm: /bin/bash -c 'mise run pr:await \($n)' timer-await-\($n)";

# The event `pr:await` reads off one poll, or null while it waits on.
#
# Input: an object with
#   kind    `issue` for an issue waiting on `shape:signed`, `pull` for a top,
#           `hold` for the stack top's hold (#5122);
#   state   `OPEN`, `CLOSED` or, for a pull request, `MERGED`;
#   labels  the issue's label names;
#   merge   the top's `mergeStateStatus`;
#   lacks   whether the top still lacks a trunk change the branch builds on;
#   age     seconds since the top's head commit was made;
#   hold    for `hold`, the record `{holder, head, began, deadline}`, or null
#           once it is released;
#   now     for `hold`, the time, in epoch seconds.
# Output: null, or `{event, exit}`: exit 0 for an event `pr:open` reruns on,
# 1 for a change that needs a hand.
def awaited:
  if .kind == "hold" then
    if .hold == null then {event: "hold-released", exit: 0}
    elif .hold.deadline <= .now then {event: "hold-expired", exit: 0}
    else null
    end
  elif .kind == "issue" then
    if .state != "OPEN" then {event: "issue-closed", exit: 1}
    elif .labels | index("shape:signed") then {event: "signed", exit: 0}
    else null
    end
  elif .state == "MERGED" then {event: "top-merged", exit: 0}
  elif .state != "OPEN" then {event: "top-closed", exit: 1}
  elif .merge == "DIRTY" then
    if (.age // 0) >= window then {event: "top-stale", exit: 0} else null end
  elif .lacks then null
  else {event: "top-current", exit: 0}
  end;
