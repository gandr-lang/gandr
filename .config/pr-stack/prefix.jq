# What a landing queues of a stack, decided from the server, the only record
# (#1264): the largest prefix that is ready (#1988), at most `cap` members
# (#2046). The stack is read bottom up, and every member green on the trunk's
# required contexts and free of conflicts joins the prefix until the first
# that is red, pending or conflicting (#2783), or until the prefix holds `cap`
# members. The tail above becomes the next stack, landed the moment its own
# bottom goes green.
#
# The merge queue merges a queued stack whole: it fits the stack into a merge
# group only up to `max_entries_to_merge` and half again, and otherwise merges
# it as one unit once every member's group is built, `max_entries_to_build`
# at a time. A 14-member stack queued at once under 3/3 merged nothing for
# 25 minutes while its bottom three were green (#2046). So a unit is at most
# `cap` members, the smaller of the two queue parameters. A queued unit below
# the cap is topped up with the green members above it (#2096): GitHub's
# stack merge appends them and leaves the queued ones' entries and their
# running groups alone, so a member that goes green while the unit builds
# joins it rather than waiting the unit's whole round. A unit at the cap,
# or with nothing green above it, takes nothing more until it merged; without
# a cap a queued unit takes nothing more.
#
# Input: an object with
#   server   the stack, bottom to top, each `{number, head}` (`chain.jq`);
#   queued   the numbers of the stack's pull requests already in the merge
#            queue;
#   carried  the numbers of the pull requests outside the stack, queued on
#            their own, whose branch the stack's top holds
#            (`carried_queued`); absent reads as none;
#   states   each member's readiness, from its number to `green`, `red`,
#            `pending` or `conflicting` (`state.jq`); a member not read is
#            pending;
#   cap      the most members one landing queues; absent or 0 reads as no
#            cap.
#
# Output: one tab-separated line:
#   wait<TAB>N                 #N, carried, is queued on its own; land once it
#                              merges, when the stack is read again;
#   queued                     every member is in the merge queue already;
#   busy<TAB>N                 #N, the stack's top queued member, is in the
#                              queue, and its unit takes nothing more: it is
#                              at the cap, there is none, or the lowest member
#                              above it is not green; the next unit lands once
#                              it merges;
#   hold<TAB>N<TAB>STATE       nothing lands: the lowest member outside the
#                              queue, #N, is red, pending or conflicting;
#   land<TAB>N                 queue the stack up to and including #N, its top;
#   land<TAB>N<TAB>M<TAB>STATE queue the stack up to and including #N; #M
#                              above it stays out, STATE being `red`,
#                              `pending`, `conflicting`, or `capped` when the
#                              unit is full.
# A landing above queued members queues only the members outside the queue,
# at most the cap less the queued ones.

. as $in
| [$in.server[].number | select(. as $n | $in.queued | index($n) | not)] as $open
| ($in.cap // 0) as $limit
| (if $limit > 0 then $limit - ($in.queued | length) else ($open | length) end) as $cap
| def state($n): $in.states["\($n)"] // "pending";
  if ($in.carried // []) != [] then
    "wait\t\($in.carried | last)"
  elif $open == [] then
    "queued"
  elif $in.queued != [] and ($limit <= 0 or $cap <= 0 or state($open[0]) != "green") then
    "busy\t\([$in.server[].number | select(. as $n | $in.queued | index($n))] | last)"
  else
    (first(range(0; $open | length) | select(state($open[.]) != "green")) // ($open | length)) as $stop
    | if $stop == 0 then
        "hold\t\($open[0])\t\(state($open[0]))"
      elif $stop > $cap then
        "land\t\($open[$cap - 1])\t\($open[$cap])\tcapped"
      elif $stop == ($open | length) then
        "land\t\($open[-1])"
      else
        "land\t\($open[$stop - 1])\t\($open[$stop])\t\(state($open[$stop]))"
      end
  end
