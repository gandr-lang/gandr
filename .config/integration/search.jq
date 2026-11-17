# One step of the head watcher's search over the first parents (#6587),
# read by `landing:watch`. A check passes on the last green head of
# `landing` and fails on a newer head. The search halves the first-parent
# line between them until it holds one commit: the first commit where the
# check fails, which names the pull request that brings the fault.
#
# The input holds `commits`, the first-parent line after the green head,
# oldest first, its last the red head, and `results`, each probed commit's
# `pass` or `fail`. The green head passes and the red head fails, so
# neither is probed. The search reads the newest pass, and the oldest fail
# after it, as the bounds.
#
# The output is `{probe: <commit>}`, the commit to run the check on next,
# or `{culprit: <commit>}`, the first commit where the check fails. An empty
# line is refused.
. as $in
| ($in.commits | length) as $n
| if $n == 0 then error("search: no commit after the green head")
  else
    ([range(0; $n) | select($in.results[$in.commits[.]] == "pass")] | max // -1) as $low
    | ([range($low + 1; $n) | select($in.results[$in.commits[.]] == "fail")] | min // ($n - 1)) as $high
    | if $high - $low == 1 then {culprit: $in.commits[$high]}
      else {probe: $in.commits[(($low + $high) / 2) | floor]}
      end
  end
