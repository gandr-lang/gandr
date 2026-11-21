# The open pull requests whose commits a branch holds past a base (#6797).
# A commit past the base that another open pull request's branch also holds
# is that pull request's, not the unit's own: a landing over that base would
# squash it under the unit's title. A pull request whose branch holds the
# unit's head stands above it, and its commits past the base are the unit's
# own and its own, so it is left out (`foreign_commits`).
#
# Input: an object with
#   number   the unit's pull request, or null before it is opened;
#   commits  the commits of the unit's branch past the base;
#   open     each other open pull request as `{number, commits, above}`:
#            `commits` the commits of its branch past the same base, `above`
#            true when its branch holds the unit's head.
# Output: each open pull request below or beside the unit that shares a
# commit with it, as `{number, commits}` with the count shared, by number.
# An empty array means the base agrees with the branch.

. as $in
| (reduce $in.commits[] as $c ({}; .[$c] = true)) as $own
| [$in.open[]
   | select(.number != $in.number and (.above | not))
   | {number, commits: ([.commits[] | select($own[.])] | length)}
   | select(.commits > 0)]
| sort_by(.number)
