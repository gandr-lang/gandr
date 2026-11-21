# The GitHub dependencies an issue owes (#2902): one line per dependency to
# set and per one set that the record does not name, or nothing.
#
# Input:
#   number      the issue's number
#   labels      its labels: [name]
#   body        its body
#   blocked_by  the issues GitHub has it blocked by: [{number, state}]
#   sub_issues  its sub-issues: [{number, state}]
#
# An issue is blocked by each issue its `## After` lists, and an epic
# (`kind:epic`) by each of its open sub-issues as well, so its page shows the
# open work and it cannot close over it. Each one GitHub lacks is a line
# `set<TAB><n><TAB><why>`, which `unit:check --fix` sets and `unit:check`
# refuses. A dependency GitHub has that neither names is a line
# `extra<TAB><n>`: the section is the record and the API the mechanism, so it
# is reported, not refused. An issue never waits on itself.

include "sections";

.number as $self
| ((.labels // []) | index("kind:epic") != null) as $epic
| [(.blocked_by // [])[].number] as $set
| [(.body // "" | after // {numbers: []}).numbers[] | select(. != $self) | {n: ., why: "`## After` lists it"}] as $listed
| (if $epic then [(.sub_issues // [])[] | select(.state == "open" and .number != $self) | {n: .number, why: "an open sub-issue of the epic"}] else [] end) as $open
| ($listed + $open | unique_by(.n)) as $wanted
| ($wanted[] | select(.n as $n | $set | index($n) | not) | "set\t\(.n)\t\(.why)"),
  ($set[] | select(. as $n | [$wanted[].n] | index($n) | not) | "extra\t\(.)")
