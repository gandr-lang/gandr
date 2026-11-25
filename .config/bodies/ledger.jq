# Whether a landing patches the features ledger rows it names, in the landing
# (#2525, `tracker.md` § the record): one line per refusal, or nothing.
#
# Input:
#   body     the body's text
#   rows     the ids of `ledger/features/` at the head
#   touched  the rows the change adds, edits or removes:
#            [{id, status, issue}], each the head's (null for a removed row)
#
# The body's `## Ledger` names a row by an item opening with its id,
# `` - `<id>` — <witness> ``; `None.` or no section names none. A named row
# must exist and be touched; a touched row the body does not name is
# refused. A declined row the change touches names its decision beside the
# issues the body closes (`Closes`, `Fixes` or `Resolves` `#n`): the merge
# closes those as completed, and `check:tracking` holds a declined row only
# by an issue open or closed as not planned (#2848).

include "sections";

(.rows // []) as $rows
| (.touched // []) as $touched
| [.body | scan("(?i)\\b(?:close[sd]?|fix(?:e[sd])?|resolve[sd]?)\\s+#([0-9]+)") | .[0] | tonumber] as $closes
| [(.body | section("Ledger") // []) | items | capture("^[-*] `(?<id>[a-z0-9][a-z0-9-]*)`").id] | unique as $named
| ($named[]
    | . as $id
    | ([$touched[] | select(.id == $id)] | first) as $row
    | if ($rows | index($id)) == null and $row == null then "`## Ledger` names `\($id)`, no row of `ledger/features/`: name a row by its id, then run the task again"
      elif $row == null then "`## Ledger` names `\($id)`, and the change does not touch its row: patch the row, or drop the item, then run the task again"
      else empty
      end),
  ($touched[]
    | select(.id as $id | $named | index($id) | not)
    | "the change touches the ledger row `\(.id)`, and `## Ledger` does not name it: add `- `\(.id)` — <witness>`, then run the task again"),
  ($touched[]
    | select(.status == "declined")
    | [(.issue // "") | scan("(?:^|\\s)#([0-9]+)") | .[0] | tonumber] as $refs
    | select(($refs | length) > 0 and all($refs[]; IN($closes[])))
    | "the declined row `\(.id)` names only \($refs | map("#\(.)") | join(", ")), which this landing closes as completed: name its decision beside it, an issue closed as not planned, then run the task again")
