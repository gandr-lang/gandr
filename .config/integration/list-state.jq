# The state that the known-red list's issue owes (#6540), read by `ci:cycle`.
# The list holds a row for a failed cycle or a take that does not merge, and
# the issue is open while it holds one. With no row the issue is closed, so
# an empty list counts as no open defect. A brake that holds is no row.
#
# Input:
#   row    whether the list holds a row: `known-red.jq`'s `page`, or, for a
#          list that stands, a cycle that does not pass or a take that does
#          not merge
#   state  the issue's state, `OPEN` or `CLOSED`, or null when no list issue
#          exists
#
# Output: `{act}`, where `act` is `reopen`, `close`, `file` or null. `file`
# files the list for its first row; a list with no row and no issue files
# nothing.

if .state == null then {act: (if .row then "file" else null end)}
elif .row and .state != "OPEN" then {act: "reopen"}
elif (.row | not) and .state == "OPEN" then {act: "close"}
else {act: null}
end
