# The open pull requests as the stacking rule reads them (`open_prs`).
#
# Input: the server's open pull requests, as the GraphQL reading in
# `stack.bash` gives them, in an array.
# Output: each as `{number, head, base, created, landing, held, stack, bot,
# hold}`: `landing` when it is in the merge queue or set to enter it
# (auto-merge), so its branch is about to be deleted and nothing new stacks on
# it (#1455); `held` when it carries the `landing` label, a `pr:land` waiting
# to queue it (#1556); `stack` the number of the linked stack holding it, or
# null (#1520); `bot` when an app such as Dependabot opened it, so nothing
# stacks on it (#2550); `hold` why it is held on purpose, or null: `owner`
# for the owner's `hold:owner` label, which outlasts a draft taken back
# (#3253), then `draft` for a draft (`pr:hold`, #2972). A held pull request
# never lands, and neither does the stack above it (`rests.jq`).

map({
  number,
  head: .headRefName,
  base: .baseRefName,
  created: .createdAt,
  landing: (.isInMergeQueue or .autoMergeRequest != null),
  held: any(.labels.nodes[]; .name == "landing"),
  stack: .stack.number,
  bot: (.author.__typename == "Bot"),
  hold: (if any(.labels.nodes[]; .name == "hold:owner") then "owner" elif .isDraft then "draft" else null end)
})
