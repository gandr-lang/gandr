# Whether a pull request's push is GitHub's rebase of a change that already
# passed (#2070, #2700): `true` skips the lanes, `false` runs them.
#
# Input:
#   committer  the pushed head's committer login (`web-flow` for GitHub's own
#              rebase)
#   before     the replaced head's patch-id against its fork from the trunk,
#              or "" when it could not be read
#   after      the pushed head's, the same way
#   required   the trunk ruleset's required contexts
#   reading    `required.jq`'s reading of the replaced head's check rollup
#              against `required`: {failed, pending}
#
# GitHub rebases a stack's members itself when a member below merges, and
# the rebase leaves the change's patch as it was: the head it replaced ran
# the lanes. That is a reason to skip them only where they passed there: no
# required context failed, none is still pending or unreported, and the
# required contexts were read at all. Any other push runs the lanes.

.committer == "web-flow"
and (.before // "") != ""
and .before == .after
and ((.required // []) | length) > 0
and ((.reading.failed // ["unread"]) | length) == 0
and ((.reading.pending // ["unread"]) | length) == 0
