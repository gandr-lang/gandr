# The rows of `artifacts.json` that a replay makes due (#6144), as
# `stale.bash` reads them. A replay moves a branch's own commits onto a base
# that moved, and keeps each generated artifact the commits hold. A row is due
# when the base's move and the own commits both touch its paths or its inputs,
# and one of the two touches its paths: then one side wrote the artifact from
# inputs that the other side changed. A row with `each: "crate"` stands for
# one row for each crate (`paths.jq`). Rows that share a check run it once,
# their names joined.
#
# Input:
#   rows    the rows of `artifacts.json`
#   moved   the paths the base moved
#   own     the paths the own commits change
#   crates  the directory names under `crates/` at the head
#
# Output: the due rows, `{name, check, record, stale}`, in the order of their
# checks. `stale` holds the exit statuses of the check that mean the artifacts
# disagree (#6786), or null when the row names none.

include "paths" {search: "./"};

. as $in
| [$in.rows[] | expanded($in.crates)
    | select(holds(.paths + .inputs; $in.moved) and holds(.paths + .inputs; $in.own)
        and (holds(.paths; $in.moved) or holds(.paths; $in.own)))]
| group_by(.check)
| map({name: (map(.name) | join(", ")), check: .[0].check, record: .[0].record, stale: (.[0].stale // null)})
