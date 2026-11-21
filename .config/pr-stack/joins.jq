# Whether `pr:open` stacks a new pull request above the top (#7188). A
# stacked change waits on the top's stack, so the change stacks only above a
# top that can merge and that it needs. A top that carries a hold, a draft, a
# top that conflicts with the trunk or one that GitHub has not read
# mergeable, and a stack that shares no path with the change, each leave the
# change on the trunk by itself.
#
# Input: an object with
#   draft      whether the top is a draft, held on purpose (`pr:hold`);
#   held       whether the top carries the label `landing`: a `pr:land` is
#              about to queue it;
#   merge      the top's `mergeStateStatus`;
#   mergeable  the top's `mergeable`: `MERGEABLE`, `CONFLICTING` or
#              `UNKNOWN`;
#   shared     the paths that the change and the top's stack both change.
# Output: `{act, why}`. `act` is `stack` or `alone`, and `why` names the
# fact that decides.

if .held then {act: "alone", why: "it carries the label landing, and a pr:land is about to queue it"}
elif .draft then {act: "alone", why: "it is a draft, held"}
elif .merge == "DIRTY" or .mergeable == "CONFLICTING" then {act: "alone", why: "it conflicts with the trunk"}
elif .mergeable != "MERGEABLE" then {act: "alone", why: "GitHub has not read it mergeable"}
elif (.shared | length) == 0 then {act: "alone", why: "the change shares no path with its stack"}
else {act: "stack", why: "the change shares \(.shared | length) paths with its stack, as \(.shared[:3] | join(" "))"}
end
