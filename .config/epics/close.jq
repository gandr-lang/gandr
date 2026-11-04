# An epic closes itself when every issue it is blocked by and every
# sub-issue it holds is closed, never with none (#3398, #4972, `tracker.md`
# § tracker-issues): what to do with one epic the closed issue blocked or sat
# under, as one `action<TAB>reason<TAB>links` line.
#
# Input:
#   repo         the repository the run is in, `owner/name`
#   closed       the number of the issue that closed
#   epic         an issue the closed one blocked or sat under: {number, repository, state, labels: [name]}
#   blocked_by   the issues that one is blocked by: [{number, repository, state}]
#   sub_issues   the sub-issues that one holds: [{number, repository, state}]; absent reads as none
#
# The epic's units are the issues it is blocked by and its sub-issues, each
# once. `close` when the epic is an open `kind:epic` in this repository with
# at least one unit and none of them open, the reason the closing comment
# naming them and the one that closed last; `list` when it would close but
# lives in another repository, whose issues this repository's token cannot
# close; `keep` otherwise, naming why. An epic with no unit never closes
# here: its units are not linked yet.
#
# `links` names, space-separated, each open sub-issue in this repository of
# an open `kind:epic` here that the epic is not blocked by, so the caller
# sets it as one and the two lists agree. It is empty otherwise.

.repo as $repo
| def named: if .repository == $repo then "#\(.number)" else "\(.repository)#\(.number)" end;
  .epic as $epic
  | (.sub_issues // []) as $subs
  | reduce (.blocked_by[], $subs[]) as $unit ([];
      if any(.[]; .number == $unit.number and .repository == $unit.repository) then . else . + [$unit] end) as $units
  | [$units[] | select(.state == "open") | named] as $open
  | [$units[] | named] as $all
  | [.blocked_by[] | named] as $blockers
  | (if $epic.state == "open" and ($epic.labels | index("kind:epic")) != null and $epic.repository == $repo
     then [$subs[] | select(.state == "open" and .repository == $repo) | select((named | IN($blockers[])) | not) | .number]
     else [] end | map(tostring) | join(" ")) as $links
  | (if $epic.state != "open" then "keep\t\($epic | named) is closed"
     elif ($epic.labels | index("kind:epic")) == null then "keep\t\($epic | named) is not an epic"
     elif ($all | length) == 0 then "keep\t\($epic | named) is blocked by nothing and holds no sub-issue: an epic closes only once its units are linked"
     elif ($open | length) > 0 then "keep\t\($epic | named): \($open | join(", ")) still open"
     elif $epic.repository != $repo then "list\t\($epic | named) is in another repository"
     else "close\tEvery issue this epic is blocked by or holds as a sub-issue is closed, the last #\(.closed): \($all | join(", ")). Reopen it to add a unit."
     end) + "\t\($links)"
