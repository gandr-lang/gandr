# What keeps the table's `reads` true to the light checks that it scopes
# (#6895). Each row names every path that its check reads, as `reads.bash`
# walks them, or a directory above it. A path of the table's `reads.every`
# selects every scoped check, so a row need not name it. A row scopes a check
# task that no group runs.
#
# Input:
#   reads  [{check, path}]: each path that a scoped check reads
#   tasks  every `check:*` task's name
#   table  the table to read; absent, `table.json`
#
# Output: one finding per line, nothing when the rows hold.

import "table" as $table;

include "rows";

(.table // $table::table[0]) as $table
| ($table.reads.checks // {}) as $rows
| ($table.reads.every // []) as $every
| ([$table.groups[][]] | unique) as $grouped
| .tasks as $names
| ($rows | keys[] | select(IN($names[]) | not)
    | "reads: it scopes \(.), which is no check task"),
  ($rows | keys[] | select(IN($grouped[]))
    | "reads: it scopes \(.), which a group of .config/gate-scope/table.json runs; a row scopes a light check alone"),
  (.reads[] | . as {check: $check, path: $path}
    | select($rows[$check] != null)
    | select(any($rows[$check][], $every[]; mapped({path: .}; $path)) | not)
    | if $path == "." then
        "\($check): it lists or searches the whole tree, so no row of the reads of .config/gate-scope/table.json can scope it"
      else
        "\($check): it reads \($path), which its row in the reads of .config/gate-scope/table.json does not name"
      end)
