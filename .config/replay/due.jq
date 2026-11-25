# The rows of the table of artifacts that need their check when a script
# replays a branch. The script puts the own commits of the branch onto a base
# that moves. It keeps each generated
# artifact of the commits. A row needs its check when the move of the base and
# the own commits both touch its paths or its inputs. One of the two must
# touch its paths: then one side writes the artifact from inputs that the
# other side changes.
#
# Only a row with a `check` can need its check. A row with `each: "crate"`
# stands for one row for each crate. Rows with the same check run it one
# time, and the result joins their names.
#
# - see: `.config/replay/artifacts.json`
# - see: `.config/replay/stale.bash`
# - see: `.config/replay/paths.jq`
# - see: #6144
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
| [$in.rows[] | checked | expanded($in.crates)
    | select(holds(.paths + .inputs; $in.moved) and holds(.paths + .inputs; $in.own)
        and (holds(.paths; $in.moved) or holds(.paths; $in.own)))]
| group_by(.check)
| map({name: (map(.name) | join(", ")), check: .[0].check, record: .[0].record, stale: (.[0].stale // null)})
