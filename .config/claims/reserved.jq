# A reserved grammar rule is not lowered (#2528): one line per syntax-ledger
# row reserved at the base that the head implements, unless the row's issue
# is open and its body names the rule, by its name or its kind.
#
# Input: {rows: [{name, kind, issue, admission, now}], issues: {"<n>": {state,
# body}}}, `rows` the base's reserved rows, `now` each one's status at the
# head (null where the head has no such rule), `issues` each cited issue as gh
# reads it (absent where gh could not read it).
.issues as $issues
| .rows[]
| select(.now == "implemented")
| . as $row
| ($issues[(.issue // "" | ltrimstr("#"))]) as $cited
| (if .issue == null then "cites no issue"
   elif $cited == null then "cites \(.issue), which gh could not read"
   elif $cited.state != "OPEN" then "cites \(.issue), which is \($cited.state | ascii_downcase)"
   elif ([.name, .kind] | any(. as $said | $cited.body | contains($said))) then empty
   elif .name == .kind then "cites \(.issue), whose body does not name `\(.name)`"
   else "cites \(.issue), whose body names neither `\(.name)` nor `\(.kind)`"
   end) as $why
| "`\($row.name)` is reserved and this change lowers it; its row \($why): name the rule in an open issue's design and cite it, or decline the rule\n  row: \($row | del(.now) | tojson)"
