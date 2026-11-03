# What keeps `table.json` true to the checks it scopes (#4911): a check that
# builds or runs the toolchain sits in a group, so a workflow change never runs
# it, and every check a group names exists. A heavy check is one whose script
# runs `cargo` beyond `cargo metadata`, the gate binary `quenchant-gates`, or
# the extension's `aube` or `node`, or one that depends on a grouped check. The
# table's `light` list names a heavy check that runs on every change anyway.
#
# Input:
#   tasks  each `check:*` task as `mise tasks ls --json` lists it: name, run
#          and depends
#   table  the table to read; absent, `table.json`
#
# Output: one finding per line, nothing when the table holds.

import "table" as $table;

(.table // $table::table[0]) as $table
| ([$table.groups[][]] | unique) as $grouped
| ([.tasks[].name]) as $names
| (.tasks[]
    | select(.name | IN($grouped[]) or IN(($table.light // [])[]) | not)
    | select((.run | tostring | test("cargo (?!metadata)|quenchant-gates|\\baube |\\bnode "))
        or any(.depends[]?; IN($grouped[])))
    | "\(.name): it builds or runs the toolchain and sits in no group of .config/gate-scope/table.json"),
  ($table.groups | to_entries[] | .key as $group | .value[]
    | select(IN($names[]) | not)
    | "\($group): it names \(.), which is no check task")
