# Which queued pull requests a stack waits on (#4168). A pull request outside
# the stack, in the merge queue or set to enter it, whose branch the stack's
# top holds, carries the stack's commits: the stack lands once it merges
# (`carried_queued`). One queued on a base that is neither the trunk nor an
# open pull request's head waits in a queue that merges nothing into the
# trunk, so the stack never waits on it: it is named, and the stack lands
# past it, its commits with it.
#
# Input: an object with
#   open   the open pull requests (`open.jq`);
#   trunk  the default branch;
#   held   the numbers of the pull requests outside the stack, queued, whose
#          branch the stack's top holds.
# Output: `{wait, off}`: `wait` the numbers the stack waits on, ascending;
# `off` each one queued off the trunk as `{number, base}`, by number.

. as $in
| [$in.open[] | select(.number | IN($in.held[]))] as $held
| def off: . as $pr | $pr.base != $in.trunk and all($in.open[]; .head != $pr.base);
  {wait: [$held[] | select(off | not) | .number] | sort,
   off: [$held[] | select(off) | {number, base}] | sort_by(.number)}
