# What `pr:watch`'s heal does with its pull request's server stack (#3615).
# A heal restacks the whole stack onto the trunk in one atomic push. A
# member in the merge queue, or set to enter it, never moves (#2531): the
# server refuses the push to its branch and with it the whole push. So a
# stack with such a member waits for it to merge, and the watch polls on.
#
# Input: an object with
#   heals    the heals this watch has run;
#   members  the stack's members, bottom to top, each `{number, red,
#            queued}`: `red` when a required check failed on its head,
#            `queued` when it is in the merge queue or set to enter it.
# Output: `{act}`: `stop` for an empty stack, a red member or a fourth heal,
# which the watch reports; `wait` with `queued`, the queued members'
# numbers, which the watch polls past; `restack` otherwise.

if (.members | length) == 0 or any(.members[]; .red) or .heals >= 3 then {act: "stop"}
elif any(.members[]; .queued) then {act: "wait", queued: [.members[] | select(.queued) | .number]}
else {act: "restack"}
end
