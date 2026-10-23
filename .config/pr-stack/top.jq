# The pull request a new one stacks on: the top of the server's open stacks.
#
# Input: the open pull requests, each `{number, head, base, created, landing,
# held}`.
# Arguments: `$own`, the branch being opened, left out of the reading;
# `$trunk`, the default branch.
# Output: `{number, head, depth, held, landing}` for the open pull request no
# other open pull request targets, on the longest chain from the trunk, the
# newest on a tie; null when no other pull request is open. A top not landing
# is read before a landing one; with every open pull request landing, the top
# is the landing chain's (#1983): the new pull request opens on it unlinked,
# for a queued stack takes no link (#1353), and when that top merges GitHub
# moves it to the trunk. `held` is the top's `landing` label: a `pr:land` is
# waiting to queue it, so `pr:open` waits for the hold to clear (#1556).

[.[] | select(.head != $own)] as $open
| def depth($pr):
    [limit(64; $pr | recurse(. as $at | if $at.base == $trunk then empty else ([$open[] | select(.head == $at.base)] | first // empty) end))]
    | length;
  [$open[] | . as $pr | select(all($open[]; .base != $pr.head)) | . + {depth: depth(.), landing: (.landing // false)}]
| (sort_by([(.landing | not), .depth, .created]) | last) as $top
| if $top == null then null else $top | {number, head, depth, held: (.held // false), landing} end
