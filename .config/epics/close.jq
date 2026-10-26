# An epic closes when its last sub-issue closes (#2536, `tracker.md`
# § tracker-issues): what to do with a closed issue's parent, as one
# `action<TAB>reason` line.
#
# Input:
#   repo         the repository the run is in, `owner/name`
#   closed       the number of the issue that closed
#   parent       the closed issue's parent: {number, repository, state, labels: [name]}
#   sub_issues   the parent's sub-issues: [{number, repository, state}]
#
# `close` when the parent is an open `kind:epic` in this repository with no
# open sub-issue left; `list` when it would close but lives in another
# repository, whose epics this repository's token cannot close; `keep`
# otherwise, naming why.

.repo as $repo
| .parent as $parent
| [.sub_issues[] | select(.state == "open") | if .repository == $repo then "#\(.number)" else "\(.repository)#\(.number)" end] as $open
| if $parent.state != "open" then "keep\tthe parent is closed"
  elif ($parent.labels | index("kind:epic")) == null then "keep\tthe parent is not an epic"
  elif ($open | length) > 0 then "keep\t\($open | join(", ")) still open"
  elif $parent.repository != $repo then "list\t\($parent.repository)#\($parent.number) is in another repository"
  else "close\tClosed by its last sub-issue #\(.closed)."
  end
