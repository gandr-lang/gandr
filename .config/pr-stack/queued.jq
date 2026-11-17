# The pull requests a push to branch `$branch` would eject (#2531), as a JSON
# array of `{number, state}`, bottom to top; empty when the push may go.
#
# Input: the open pull requests (`open_prs`). A push to a branch whose pull
# request is in the merge queue, set to enter it (`landing`), or held for it
# by a waiting `pr:land` (`held`, the `landing` label), ejects it; a push to
# a branch below such a pull request moves the base it was queued on and
# ejects it too, with every member above. The pull requests above a branch
# are those based on it, transitively. `state` is `queued` or `held`.

def above($prs; $head): $prs[] | select(.base == $head) | ., above($prs; .head);

. as $prs
| [$prs[] | select(.head == $branch)] as $own
| [$own[], ($own[] | above($prs; .head))]
| map(select(.landing or .held) | {number, state: (if .landing then "queued" else "held" end)})
