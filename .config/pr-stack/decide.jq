# How `pr:land` lands a pull request, decided from its stack on the server,
# the only record (#1264).
#
# Input: an object with
#   server  the pull request's stack, bottom to top, each `{number, head}`
#           (`chain.jq`);
#   own     the checked-out branch;
#   queued  the numbers of the stack's pull requests already in the merge
#           queue.
#
# Output: one tab-separated line:
#   single              land the one pull request;
#   wait<TAB>N          #N below is queued on its own; land once it merges,
#                       when the stack is read again;
#   stack<TAB>N         restack and queue the stack whose top is #N;
#   refuse<TAB>MESSAGE  stop, naming why.
#
# A stack lands whole from its top: the obligations are measured on the
# checked-out tree, which is the top's.

def chain: [.server[] | "#\(.number)"] | join(" ← ");
. as $in
| [$in.server[:-1][] | .number | select(. as $n | $in.queued | index($n))] as $waiting
| if ($in.server | length) <= 1 then
    "single"
  elif ($waiting | length) > 0 then
    "wait\t\($waiting | last)"
  elif $in.own != $in.server[-1].head then
    "refuse\tthe checked-out branch is not the top of the server stack \($in | chain); land it with `pr:land` from #\($in.server[-1].number)'s branch"
  else
    "stack\t\($in.server[-1].number)"
  end
