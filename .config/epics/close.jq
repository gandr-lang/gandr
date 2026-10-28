# An epic closes itself when every issue it is blocked by is closed, never
# with none (#3398, `tracker.md` § tracker-issues): what to do with one epic
# the closed issue blocked, as one `action<TAB>reason` line.
#
# Input:
#   repo         the repository the run is in, `owner/name`
#   closed       the number of the issue that closed
#   epic         an issue the closed one blocked: {number, repository, state, labels: [name]}
#   blocked_by   the issues that one is blocked by: [{number, repository, state}]
#
# `close` when the epic is an open `kind:epic` in this repository blocked by
# at least one issue and none of them open, the reason the closing comment
# naming them and the one that closed last; `list` when it would close but
# lives in another repository, whose issues this repository's token cannot
# close; `keep` otherwise, naming why. An epic blocked by nothing never
# closes here: its units are not linked yet.

.repo as $repo
| def named: if .repository == $repo then "#\(.number)" else "\(.repository)#\(.number)" end;
  .epic as $epic
  | [.blocked_by[] | select(.state == "open") | named] as $open
  | [.blocked_by[] | named] as $all
  | if $epic.state != "open" then "keep\t\($epic | named) is closed"
    elif ($epic.labels | index("kind:epic")) == null then "keep\t\($epic | named) is not an epic"
    elif ($all | length) == 0 then "keep\t\($epic | named) is blocked by nothing: an epic closes only once its units are linked"
    elif ($open | length) > 0 then "keep\t\($epic | named): \($open | join(", ")) still open"
    elif $epic.repository != $repo then "list\t\($epic | named) is in another repository"
    else "close\tEvery issue this epic is blocked by is closed, the last #\(.closed): \($all | join(", ")). Reopen it to add a unit."
    end
