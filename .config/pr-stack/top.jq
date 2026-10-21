# The pull request a new one stacks on: the top of the server's open stacks.
#
# Input: the open pull requests, each `{number, head, base, created}`.
# Arguments: `$own`, the branch being opened, left out of the reading;
# `$trunk`, the default branch.
# Output: `{number, head, depth}` for the open pull request no other open pull
# request targets, on the longest chain from the trunk, the newest on a tie;
# null when no other pull request is open.

[.[] | select(.head != $own)] as $open
| def depth($pr):
    [limit(64; $pr | recurse(. as $at | if $at.base == $trunk then empty else ([$open[] | select(.head == $at.base)] | first // empty) end))]
    | length;
  [$open[] | . as $pr | select(all($open[]; .base != $pr.head)) | . + {depth: depth(.)}]
| (sort_by([.depth, .created]) | last) as $top
| if $top == null then null else $top | {number, head, depth} end
