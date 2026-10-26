# Whether a landing patches the features ledger rows it names, in the landing
# (#2525, `tracker.md` § the record): one line per refusal, or nothing.
#
# Input:
#   pr       the pull request's number, or null before it has one (`pr:open`)
#   body     the body's text
#   rows     the ids of `ledger/features.sql` at the head
#   touched  the rows the change adds, edits or removes: [{id, since, status}],
#            `since` and `status` the head's (null for a removed row)
#
# The body's `## Ledger` names a row by an item opening with its id,
# `` - `<id>` — <witness> ``; `None.` or no section names none. A named row
# must exist and be touched, and once the pull request has a number its
# `since` carries `#<pr>` where the row has a `since`: an implemented or
# partial row (a planned or declined one keeps `since` NULL, the table's
# CHECK); a touched row the body does not name is refused.

include "sections";

(.pr) as $pr
| (.rows // []) as $rows
| (.touched // []) as $touched
| [(.body | section("Ledger") // []) | items | capture("^[-*] `(?<id>[a-z0-9][a-z0-9-]*)`").id] | unique as $named
| ($named[]
    | . as $id
    | ([$touched[] | select(.id == $id)] | first) as $row
    | if ($rows | index($id)) == null and $row == null then "`## Ledger` names `\($id)`, no row of `ledger/features.sql`: name a row by its id, then run the task again"
      elif $row == null then "`## Ledger` names `\($id)`, and the change does not touch its row: patch the row (its `since` with this pull request's number), or drop the item, then run the task again"
      elif $pr != null and ($row.status | IN("implemented", "partial")) and (($row.since // "") | test("#\($pr)\\b") | not) then "`## Ledger` names `\($id)`, and its `since` (`\($row.since // "NULL")`) lacks #\($pr): add it, then run the task again"
      else empty
      end),
  ($touched[]
    | select(.id as $id | $named | index($id) | not)
    | "the change touches the ledger row `\(.id)`, and `## Ledger` does not name it: add `- `\(.id)` — <witness>`, then run the task again")
