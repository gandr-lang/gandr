# The workflow runs a cut past a red member made stale (#5073). A cut moves
# the members above the red one to new heads, so a run still queued or
# running on a moved branch at any other head reads nothing. A merge group
# of a cut pull request, the red one or a moved one, holds a head no member
# has any more: the queue removed the red one, and a member in the queue is
# never moved (`heal.jq`), so its group's run reads nothing either.
#
# Input: an object with
#   runs     the repository's queued and running workflow runs, each `{id,
#            event, head_branch, head_sha, status}`;
#   heads    each moved branch's new head, `{"<branch>": "<sha>"}`;
#   numbers  the cut pull requests' numbers, the red one and the moved ones;
#   trunk    the trunk of `trunk.bash`.
# Output: the stale runs' ids, ascending.

.heads as $heads
| .numbers as $numbers
| ("gh-readonly-queue/" + .trunk + "/pr-") as $group
| [.runs[]
    | select(.status != "completed")
    | select(
        ($heads[.head_branch] != null and .head_sha != $heads[.head_branch])
        or (.event == "merge_group"
          and (.head_branch | startswith($group))
          and ([.head_branch[($group | length):] | capture("^(?<n>[0-9]+)-") | .n | tonumber] | any(IN($numbers[])))))
    | .id]
| sort
