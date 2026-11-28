# The checks a gate runs for a change (#4911). A gate whose change touches
# only the workflow built and ran the whole Rust wall, though the integration
# cycle runs every check before `main` moves. So the gate reads the paths the
# branch changes and runs the checks `table.json` maps them to.
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
# The integration cycle runs every check. So the gate of the landing
# (`mise run check`) keeps only the heavy checks that the `landing` list of
# the table names. The hosts of the lanes cannot carry the full suite before
# each pull request.
# - see: #5458, #5438
#
# The queue on `landing` runs only a part of the checks. So the gate runs
# Clippy and the compiler policy (`check:landing`). It runs the item comments
# of the corpus (`check:corpus-comments`). A parser change can move the
# uncommented items.
# - see: #6365
#
# The gate runs `check:doc` and `check:witnesses`, for a broken link or a
# renamed witness. It runs `check:syntax-exemplars`, the same verification as
# the test of the dispatcher over the ledger exemplars.
# - see: #6433, #6430
#
# For a change of the corpus or of a crate, the gate runs `check:corpus`,
# `check:corpus-format` and `check:corpus-goldens`. They refuse a stale
# golden, a source with a refusal and no golden, and a source out of the
# sugared form. The gate runs `check:tests-enforcing` over the packages that
# the change touches, and not over their dependents. Each light check takes
# seconds, so it stays.
# - see: #6489, #6595
#
# A row's path is a file, a directory that ends in `/`, or a glob
# (`rows.jq`). The globs
# give `check:prose` the paths it reads (#6648): every `.gandr` file and each
# crate's README. A `.rs` path whose change touches `//` comments alone
# (`comments.bash`) takes the table's `comments` groups, not its row's. Such
# a comment compiles to no item and no documentation, so the change runs no
# `check:doc` and no `check:corpus`.
#
# A light check runs on every change, unless the table's `reads` scopes it
# (#6895). A scoped check runs when the change touches a path of its row or a
# path of `reads.every`, such as the tools' pins. A path that no row of
# `paths` maps runs every scoped check too, as it selects every group. A
# change that touches none of them leaves the check's verdict as the base's.
# `check:gate-scope` holds each row to the paths that its check reads
# (`reads.jq`).
#
# Each row of the table's `adds` maps paths to groups. A path takes the groups
# of its `adds` rows beside the groups of its first row. These rows give
# `check:prose` the files whose `#` comments it reads. They map a file by its
# extension or its name, as the reader names its syntax, and a script with no
# extension by its directory. So a crate's `Cargo.toml` runs the Rust wall and
# the prose check, and a task file runs the prose check alone.
# - see: #7623 — the `#` comments under the prose gate's rule
#
# Input:
#   tasks     every `check:*` task's name
#   changed   the paths the change touches
#   comments  the changed `.rs` paths whose edits are `//` comments alone;
#             absent, none
#   landing   true for the landing's gate; absent, every check the change
#             selects
#   table     the table to read; absent, `table.json`
#
# Output: the checks to run, sorted.

import "table" as $table;

include "rows";

(.landing // false) as $landing
| (.table // $table::table[0]) as $table
| ($table.groups | keys) as $every
| (.comments // []) as $comments
| ([.changed[] as $path
    | (if $table.comments != null and ($path | IN($comments[])) then $table.comments
       else first($table.paths[] | select(mapped(.; $path)) | .groups) // $every
       end)[], (($table.adds // [])[] | select(mapped(.; $path)) | .groups[])]
   | unique) as $chosen
| ([$table.groups[][]] | unique) as $grouped
| ($table.reads.checks // {}) as $rows
| .changed as $changed
| any($changed[]; . as $path
    | any(($table.reads.every // [])[]; mapped({path: .}; $path))
      or (any($table.paths[]; mapped(.; $path)) | not)) as $whole
| [.tasks[] | select(. as $task
    | if $task | IN($grouped[]) then any($chosen[]; . as $group | $task | IN($table.groups[$group][]))
      elif $rows[$task] == null or $whole then true
      else any($changed[]; . as $path | any($rows[$task][]; mapped({path: .}; $path)))
      end)]
| map(select(($landing | not) or (IN($grouped[]) | not) or IN(($table.landing // [])[])))
| sort
