# The checks a gate runs for a change (#4911). A gate whose change touches
# only the workflow built and ran the whole Rust wall, though the merge group
# runs every check before a landing. So the gate reads the paths the branch
# changes and runs the checks `table.json` maps them to.
#
# The table names groups of heavy checks: `rust` (the build, the lints, the
# documentation and the test suites), `corpus` (the driver over the corpus
# roots and the ledger exemplars) and `extension` (the VS Code extension and its
# smoke). Each row of `paths` maps a path to the groups it selects: a row whose
# path ends in `/` maps every path under it, any other row maps that file. The
# first row that maps a path decides it, so a narrower row stands above a wider
# one. A path no row maps selects every group. A check no group names is light
# and always runs.
#
# Six lanes ran the full suite on their hosts before each pull request opened,
# and the hosts could not carry that load (#5458). The integration cycle runs
# every check (#5438), so the landing's gate (`mise run check`) keeps only the
# heavy checks that the table's `landing` list names. These are Clippy and the
# compiler policy (`check:landing`), and the item comments of the corpus
# (`check:corpus-comments`). A parser change can move the comment ledger. The
# queue on `landing` does not run the comment check, so the gate runs it
# (#6365). The queue runs no rustdoc and no witness check either, so a broken
# link or a renamed witness reached `landing` (#6433). Nor does it run the
# dispatcher's test of the ledger's exemplars, so a ledger exemplar that no
# longer verifies reached `landing` (#6430). The gate runs `check:doc`,
# `check:witnesses` and `check:syntax-exemplars` too, the last of which runs
# the same verification as that test. A corpus change reached `landing` with
# a stale golden, a refusing source with no golden, or a source out of the
# sugared form (#6489). So the gate runs `check:corpus`, `check:corpus-format`
# and `check:corpus-goldens` for a change under `corpus/` or `crates/`. The
# light checks stay, since each takes seconds.
#
# Input:
#   tasks    every `check:*` task's name
#   changed  the paths the change touches
#   landing  true for the landing's gate; absent, every check the change
#            selects
#   table    the table to read; absent, `table.json`
#
# Output: the checks to run, sorted.

import "table" as $table;

def mapped($row; $path):
  $row.path == $path or (($row.path | endswith("/")) and ($path | startswith($row.path)));

(.landing // false) as $landing
| (.table // $table::table[0]) as $table
| ($table.groups | keys) as $every
| ([.changed[] as $path | (first($table.paths[] | select(mapped(.; $path)) | .groups) // $every)[]] | unique) as $chosen
| ([$table.groups[][]] | unique) as $grouped
| [.tasks[] | select(. as $task | ($task | IN($grouped[]) | not) or any($chosen[]; . as $group | $task | IN($table.groups[$group][])))]
| map(select(($landing | not) or (IN($grouped[]) | not) or IN(($table.landing // [])[])))
| sort
