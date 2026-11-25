# The checks of the landing's gate, `mise run check`, for a change. The gate
# runs the cheap set of `landing` and the prose check of a pull request on
# each change. It also runs each check of the table's `gate` list that the
# change selects. No other step before `landing` runs such a check. Without
# it, the integration cycle refuses the change one cycle later.
# - see: #8224, #8230, #8337
#
# Input:
#   selected  the checks that `select.jq` selects for the change
#   table     the table to read; absent, `table.json`
#
# Output: the checks to run, the cheap set first.

import "table" as $table;

(.table // $table::table[0]) as $table
| .selected as $selected
| ["check:landing", "check:prose"]
  + [($table.gate // [])[] | select(IN($selected[]))]
