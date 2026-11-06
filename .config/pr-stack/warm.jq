# Which build units `wt:warm` removes from the build directory it copied
# into a new worktree (#5137). rustc writes into a unit's dep-info each value
# that `env!` reads and each source outside the package. Cargo does not
# compare `CARGO_MANIFEST_DIR` between two checkouts. So a copied unit that
# reads a file through it stays fresh in the new worktree, and the unit then
# reads the primary worktree's file. A unit whose dep-info names a source of
# the primary is removed, and cargo builds it again in the new worktree. A
# path under the primary's `target/` is a build product, and the copy holds
# the same product, so that path keeps its unit.
#
# Input: an object with
#   root   the primary worktree's path;
#   named  each dep-info line that names a path at or under `root`, as
#          `grep` prints it: `<dep-info path>:<line>`. An `env-dep` line
#          names the path after its first `=`, and a `checksum` line names
#          its last field.
#
# Output: the directory of each unit to remove, sorted and unique. A unit's
# dep-info is `<profile>/build/<package>/<hash>/out/<name>.d`, and its
# directory is `<profile>/build/<package>/<hash>`. A dep-info file in
# another place names no unit that cargo reads.
.root as $root
| [.named[]
   | capture("^(?<info>[^:]+):(?<line># .*)$")
   | (.line
      | if startswith("# env-dep:") then sub("^[^=]*="; "")
        else split(" ") | last
        end) as $path
   | select($path == $root or ($path | startswith($root + "/")))
   | select($path | startswith($root + "/target/") | not)
   | .info
   | select(test("/build/[^/]+/[0-9a-f]{16}/out/[^/]+\\.d$"))
   | sub("/out/[^/]+\\.d$"; "")]
| unique
