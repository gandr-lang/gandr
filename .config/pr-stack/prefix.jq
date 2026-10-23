# What a landing queues of a stack, decided from the server, the only record
# (#1264): the largest prefix that is ready (#1988), at most `cap` members
# (#2046). The stack is read bottom up, and every member green on the trunk's
# required contexts joins the prefix until the first that is red or pending,
# or until the prefix holds `cap` members. The tail above becomes the next
# stack, landed the moment its own bottom goes green.
#
# The merge queue merges a queued stack whole: it fits the stack into a merge
# group only up to `max_entries_to_merge` and half again, and otherwise merges
# it as one unit once every member's group is built, `max_entries_to_build`
# at a time. A 14-member stack queued at once under 3/3 merged nothing for
# 25 minutes while its bottom three were green (#2046). So a unit is at most
# `cap` members, the smaller of the two queue parameters, and while any member
# of the stack is queued nothing more is queued: the next unit goes in once
# the queued one merged, so each merges in one round.
#
# Input: an object with
#   server   the stack, bottom to top, each `{number, head}` (`chain.jq`);
#   queued   the numbers of the stack's pull requests already in the merge
#            queue;
#   carried  the numbers of the pull requests outside the stack, queued on
#            their own, whose branch the stack's top holds
#            (`carried_queued`); absent reads as none;
#   states   each member's required contexts outside the queue, from its
#            number to `green`, `red` or `pending` (`required.jq`); a member
#            not read is pending;
#   cap      the most members one landing queues; absent or 0 reads as no
#            cap.
#
# Output: one tab-separated line:
#   wait<TAB>N                 #N, carried, is queued on its own; land once it
#                              merges, when the stack is read again;
#   queued                     every member is in the merge queue already;
#   busy<TAB>N                 #N, the stack's top queued member, is in the
#                              queue; the next unit lands once it merges;
#   hold<TAB>N<TAB>STATE       nothing lands: the lowest member outside the
#                              queue, #N, is red or pending;
#   land<TAB>N                 queue the stack up to and including #N, its top;
#   land<TAB>N<TAB>M<TAB>STATE queue the stack up to and including #N; #M
#                              above it stays out, STATE being `red`,
#                              `pending`, or `capped` when the unit is full.

. as $in
| [$in.server[].number | select(. as $n | $in.queued | index($n) | not)] as $open
| (if ($in.cap // 0) > 0 then $in.cap else ($open | length) end) as $cap
| def state($n): $in.states["\($n)"] // "pending";
  if ($in.carried // []) != [] then
    "wait\t\($in.carried | last)"
  elif $open == [] then
    "queued"
  elif $in.queued != [] then
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
