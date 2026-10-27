# The hold a landing of pull request `$n` rests on (#3253): `$n` itself or the
# nearest pull request below it on its base chain held on purpose, `pr:hold`'s
# draft or the owner's `hold:owner`. A held pull request is left out of every
# stack (`landable_prs`), so the chain above it reads as a stack of its own
# whose bottom is based on the held branch; queued, it would merge into that
# branch, or carry the held commits to the trunk once restacked by hand. The
# landing refuses it instead, naming the hold, until `pr:release` or a restack
# onto the trunk.
#
# Input: the open pull requests (`open_prs`), each `{number, head, base,
# hold}`, held ones among them.
# Arguments: `$n`, the pull request; `$trunk`, the default branch.
# Output: `{number, hold}` for the hold, or null when nothing at or below `$n`
# is held, or `$n` is not open.

. as $open
| def below($pr): $pr | if .base == $trunk then empty else ([$open[] | select(.head == $pr.base)] | first // empty) end;
  [$open[] | select(.number == $n)] | first
| if . == null then null else [limit(64; recurse(below(.))) | select(.hold != null)] | first // null | if . == null then null else {number, hold} end end
