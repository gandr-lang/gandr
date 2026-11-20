# The paths that a change shares with the top's stack, less each generated
# file (#7207). A task writes a generated file from its inputs, so two
# changes that both write it share no edit: the later one writes it again
# when its rebase replays it (#6144). The rows of
# `.config/replay/artifacts.json` name the generated files, and
# `joins.jq` reads the paths that this program leaves.
#
# Input: an object with
#   shared  the paths that the change and the top's stack both change;
#   rows    the rows of `artifacts.json`;
#   crates  the directory names under `crates/` at the head.
# Output: the shared paths that no row's paths hold, in their order.

include "paths" {search: "../replay"};

. as $in
| [$in.rows[] | expanded($in.crates) | .paths[]] as $generated
| [$in.shared[] | select(holds($generated; [.]) | not)]
