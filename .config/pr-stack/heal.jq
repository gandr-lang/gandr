# What `pr:watch`'s heal does with its pull request's server stack (#3615).
# A heal restacks the whole stack onto the trunk in one atomic push. A
# member in the merge queue, or set to enter it, never moves (#2531): the
# server refuses the push to its branch and with it the whole push. So a
# stack with such a member waits for it to merge, and the watch polls on.
#
# A red member below the watched one is its own seat's (#4642). The members
# above it restack past it when none of them changes a path it changes: their
# own commits leave its commits, onto the member below it or the trunk, and
# the red member waits alone. A member above it that shares a path, or a
# second red member, stops the heal. A red member at or above the watched one
# stops it as well: the watched one is that member's, or lands below it.
#
# Input: an object with
#   heals    the heals this watch has run;
#   own      the watched pull request's number;
#   members  the stack's members, bottom to top, each `{number, red,
#            queued, paths}`: `red` when a required check failed on its head
#            or the queue removed it for `failed_checks` (#3745), `queued`
#            when it is in the merge queue or set to enter it, and `paths`
#            the paths its own commits change.
# Output: `{act}`: `stop` for an empty stack, a fourth heal or a red member
# no restack passes, which the watch reports; `wait` with `queued`, the
# queued members' numbers, which the watch polls past; `past` with `red`,
# the red member's number, and `chain`, the members left once it is cut out;
# `restack` otherwise.

.own as $own
| .members as $members
| ([$members[] | .number] | index($own)) as $at
| ([range(0; $members | length) | select($members[.].red)] | first) as $red
| def queued_wait($of): {act: "wait", queued: [$of[] | select(.queued) | .number]};
if ($members | length) == 0 or .heals >= 3 then {act: "stop"}
elif $red == null then
  if any($members[]; .queued) then queued_wait($members) else {act: "restack"} end
elif $at == null or $red >= $at then {act: "stop"}
else
  ($members[$red + 1:]) as $above
  | ($members[$red].paths // []) as $paths
  | if any($above[]; .red) then {act: "stop"}
    elif any($above[]; any((.paths // [])[]; IN($paths[]))) then {act: "stop"}
    elif any($above[]; .queued) then queued_wait($above)
    else {act: "past", red: $members[$red].number, chain: [$members[] | select(.number != $members[$red].number) | .number]}
    end
end
