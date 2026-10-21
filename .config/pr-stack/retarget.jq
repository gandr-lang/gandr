# The open pull requests a landing would close: each based on the branch of a
# pull request that lands, and not landing itself. GitHub deletes a merged
# pull request's branch and closes every open pull request still based on it,
# unmerged, unless a linked stack carries it; retargeted to the trunk first,
# each survives the merge, and `pr:land` from its top rebases it later.
#
# Input: the open pull requests, each `{number, head, base, created}`.
# Arguments: `$landing`, the numbers of the pull requests the landing merges.
# Output: the pull requests to retarget, each `{number, base}`, by number.

. as $open
| [$open[] | select(.number | IN($landing[])) | .head] as $deleted
| [$open[] | select((.number | IN($landing[]) | not) and (.base | IN($deleted[])))]
| sort_by(.number)
| map({number, base})
