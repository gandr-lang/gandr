# What `pr:open` does when it reads the stack top again after measuring
# (#3849). The obligations are measured from the top's head, the fork the
# branch's own commits sit on. A pull request opened above that top while
# the measurement ran leaves the fork as it was, so the branch restacks onto
# the new top and opens there without measuring again. A busy stack moves
# its top every few minutes, and refusing each move starved `pr:open`.
#
# Input: an object with
#   top     the top the branch stacked on before measuring, `{number, head}`
#           or null;
#   now     the top read after measuring, the same shape;
#   kept    the measured top's head is still below the branch: false when
#           the top was restacked under it;
#   builds  `now`'s head holds the measured fork, so `now` stacks above it;
#   shared  the paths both `now`'s own changes and the branch's change.
# Output: `{act: "stay"}` while the top is the one measured on;
# `{act: "restack", onto}`, `onto` the new top, when it builds on the fork
# and shares no path; otherwise `{act: "refuse", why}`.

def named: if . == null then "none" else "#\(.number)" end;

if (.kept | not) then
  {act: "refuse", why: "the stack top \(.top | named) was restacked while the obligations were measured"}
elif .now.number == .top.number then {act: "stay"}
elif .now == null then
  {act: "refuse", why: "the stack top \(.top | named) left the stack while the obligations were measured"}
elif (.builds | not) then
  {act: "refuse", why: "the stack top moved from \(.top | named) to \(.now | named), which does not stack on the measured fork"}
elif .shared != [] then
  {act: "refuse", why: "the stack top moved from \(.top | named) to \(.now | named), which changes \(.shared | map("`\(.)`") | join(", ")) as this branch does"}
else {act: "restack", onto: .now}
end
