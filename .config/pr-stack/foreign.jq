# The commits of a branch that are another unit's (#4638), each with the
# pull requests that work its unit. A copy of another pull request's commit
# stays in a branch when that pull request restacks, and every member stacked
# above the branch then carries it into its merge group. `pr:open` refuses a
# branch whose own commits hold one (`stack.bash`'s `foreign_commits`), and
# `stall:watch` pages an open pull request whose commits hold one
# (`.config/stall/facts.jq`).
#
# Input: `{units, commits, pulls}`: the issues the branch's pull request works,
# its own commits `{oid, subject, body}`, and the pull requests to name each
# foreign unit by, `{number, body, head}`; `pulls` absent reads as none.
# Output: the foreign commits, as `targets.jq`'s `foreign` reads them.

include "targets" {search: "../claims"};

foreign(.units; .commits; .pulls // [])
