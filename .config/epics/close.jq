# An epic's closing is a ruling, not an event (#2973, `tracker.md`
# § tracker-issues): what to do with a closed issue's parent, as one
# `action<TAB>reason` line. The workflow closes no epic.
#
# Input:
#   repo         the repository the run is in, `owner/name`
#   closed       the number of the issue that closed
#   parent       the closed issue's parent: {number, repository, state, labels: [name]}
#   sub_issues   the parent's sub-issues: [{number, repository, state}]
#
# `ask` when the parent is an open `kind:epic` in this repository with no
# open sub-issue left, the reason the comment asking for the ruling; `list`
# when it would ask but lives in another repository, whose epics this
# repository's token cannot label; `keep` otherwise, naming why.

.repo as $repo
| .parent as $parent
| [.sub_issues[] | select(.state == "open") | if .repository == $repo then "#\(.number)" else "\(.repository)#\(.number)" end] as $open
| if $parent.state != "open" then "keep\tthe parent is closed"
  elif ($parent.labels | index("kind:epic")) == null then "keep\tthe parent is not an epic"
  elif ($open | length) > 0 then "keep\t\($open | join(", ")) still open"
  elif $parent.repository != $repo then "list\t\($parent.repository)#\($parent.number) is in another repository"
  else "ask\tEvery filed sub-issue is closed, the last #\(.closed). Close this epic with its ruling, or file its next unit under it (`mise run issue:file <title> <body> --epic \($parent.number)`, which takes `needs:close-ruling` off)."
  end
