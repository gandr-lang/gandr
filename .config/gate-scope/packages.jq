# The packages the Rust checks of `mise run check` run over (#5014). #4911's
# table selects the `rust` group for any path under `crates/`, and each of
# those checks ran over the whole workspace. A change can only break the
# packages it touches and the packages that depend on them, so the gate runs
# over those alone. The merge group still runs every check over the whole
# workspace before a landing.
#
# A path that the table maps to the `rust` group, as `select.jq` reads it,
# selects the package whose directory holds it. A dependency of any kind
# counts, so the set grows by every package that depends on one in it, until
# it holds still. A `rust` path that no package directory holds selects the
# whole workspace: `Cargo.toml`, `Cargo.lock`, `rust-toolchain.toml`, the
# nextest and clippy configuration, and any other file the table maps that
# way. A set that holds every package is the whole workspace too.
#
# With `touched`, the set does not grow. `check:witnesses` reads that set
# (#6433): a witness names a test of its item's own crate, and the witness
# gate refuses a witness that names a test of another crate. So a change
# breaks only the witnesses of the packages it touches.
#
# Input:
#   changed   the paths the change touches
#   packages  the workspace's packages: [{name, dir, deps: [name]}], `dir`
#             the package's directory relative to the root, with no
#             trailing `/`
#   touched   true for the touched packages alone; absent, the set grows
#   table     the table to read; absent, `table.json`
#
# Output: `"workspace"`, or the package names to run over, sorted. A change
# that selects no `rust` path gives `[]`.

import "table" as $table;

def mapped($row; $path):
  $row.path == $path or (($row.path | endswith("/")) and ($path | startswith($row.path)));

(.table // $table::table[0]) as $table
| (.touched // false) as $only
| ($table.groups | keys) as $every
| .packages as $packages
| [.changed[] as $path
    | select((first($table.paths[] | select(mapped(.; $path)) | .groups) // $every) | index("rust"))
    | (first($packages[] | select(.dir as $dir | $path | startswith($dir + "/")) | .name) // null)] as $touched
| if any($touched[]; . == null) then "workspace"
  else
    def grow: . as $set
      | ($set + [$packages[] | select(any(.deps[]; IN($set[]))) | .name] | unique) as $next
      | if ($next | length) == ($set | length) then $set else $next | grow end;
    ($touched | unique | if $only then . else grow end) as $set
    | if ($set | length) > 0 and ($set | length) == ($packages | length) then "workspace" else $set end
  end
