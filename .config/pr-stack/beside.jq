# The pull request a just-opened one stands beside: two `pr:open`s that read
# the same top at once open on one base, and neither links into the stack.
# #5339 and #5340 opened two seconds apart on one base; the stack went on
# from #5340, and #5339 later reached the queue on its own and conflicted.
# The later of the two moves onto the earlier (`pr:open`).
#
# Input: the open pull requests (`landable_prs`), each `{number, base, bot}`.
# Arguments: `$n`, the pull request just opened; `$base`, its base branch.
# Output: the number of the newest pull request opened before `$n` on the
# same base, or null when none stands beside it. A pull request an app
# opened lands on its own and stands beside none.

[.[] | select(.base == $base and .number < $n and (.bot // false | not)) | .number] | max
