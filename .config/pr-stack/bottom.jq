# A stack's bottom standing off the trunk (#4168): its base is neither the
# trunk nor an open pull request's head, so no landing reaches the trunk from
# it. A branch left behind by a merged pull request is one: a stack link
# into a server stack holding the merged pull request bases the bottom on
# its branch again, and GitHub then keeps the branch. Queued there, the
# bottom waits in a queue that merges nothing into the trunk. `land_prefix`
# retargets such a bottom to the trunk before any queueing, when its base
# merged or is gone, and refuses it by name otherwise.
#
# Input: the open pull requests (`open.jq`).
# Arguments: `$n`, the stack's bottom; `$trunk`, the default branch.
# Output: the bottom as `{number, base, landing, stack}` when it stands off
# the trunk; null when its base is the trunk or an open pull request's head,
# or when it is not open.

. as $open
| ([$open[] | select(.number == $n)] | first) as $pr
| if $pr == null or $pr.base == $trunk or any($open[]; .head == $pr.base) then
    null
  else
    $pr | {number, base, landing, stack}
  end
