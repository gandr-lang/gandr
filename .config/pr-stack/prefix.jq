# What a landing queues of a stack, decided from the server, the only record
# (#1264): the largest prefix that is ready (#1988). The members already in
# the merge queue are skipped; above them the stack is read bottom up, and
# every member green on the trunk's required contexts joins the prefix until
# the first that is red or pending. The tail above that one becomes the next
# stack, and is landed the moment its own bottom goes green.
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
#            not read is pending.
#
# Output: one tab-separated line:
#   wait<TAB>N                 #N, carried, is queued on its own; land once it
#                              merges, when the stack is read again;
#   queued                     every member is in the merge queue already;
#   hold<TAB>N<TAB>STATE       nothing lands: the lowest member outside the
#                              queue, #N, is red or pending;
#   land<TAB>N                 queue the stack up to and including #N, its top;
#   land<TAB>N<TAB>M<TAB>STATE queue the stack up to and including #N; #M
#                              above it is red or pending and stays out.

. as $in
| [$in.server[].number | select(. as $n | $in.queued | index($n) | not)] as $open
| def state($n): $in.states["\($n)"] // "pending";
  if ($in.carried // []) != [] then
    "wait\t\($in.carried | last)"
  elif $open == [] then
    "queued"
  else
    (first(range(0; $open | length) | select(state($open[.]) != "green")) // ($open | length)) as $stop
    | if $stop == 0 then
        "hold\t\($open[0])\t\(state($open[0]))"
      elif $stop == ($open | length) then
        "land\t\($open[-1])"
      else
        "land\t\($open[$stop - 1])\t\($open[$stop])\t\(state($open[$stop]))"
      end
  end
