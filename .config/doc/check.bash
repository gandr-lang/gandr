#!/usr/bin/env bash
# `check:doc`: the private-item rustdoc with each rustdoc lint denied, once
# with the default features and once with every feature on (#6508). Each pass
# writes Cargo's JSON messages, and the check prints each rendered diagnostic
# from them. The check stops at the first pass that fails.
#
# Over the whole workspace, the check keeps the messages of each pass in the
# build directory, `units-doc-default.jsonl` and `units-doc.jsonl`, and
# `ci:prune-docs` reads them as the units that the passes build. A second
# pass of its own would document 50 crates again at each change of the set
# of features. A scoped run (`GATE_SCOPE`) builds a part of the workspace, so
# it keeps no list, and each run first removes the lists of an earlier run.
#
# Usage: check.bash
set -euo pipefail
root=$(cd "${BASH_SOURCE[0]%/*}/../.." && pwd)
dir=${CARGO_TARGET_DIR:?check:doc names its build directory}
scope=${GATE_SCOPE:---workspace}
read -ra scoped <<< "$scope"
mkdir -p "$dir"
rm -f "$dir/units-doc-default.jsonl" "$dir/units-doc.jsonl"
messages=$(mktemp)
trap 'rm -f "$messages"' EXIT
# One pass: `$1` the list it keeps, then the feature arguments of `cargo doc`.
pass() {
  local list=$1 status=0
  shift
  "$root/.config/mise/gated" "$root/.config/mise/scope" cargo doc "${scoped[@]}" "$@" \
    --locked --no-deps --document-private-items --message-format json > "$messages" || status=$?
  jq -rj 'select(.reason == "compiler-message") | .message.rendered // empty' "$messages" >&2
  (( status == 0 )) || exit "$status"
  if [[ $scope == --workspace ]]; then cp "$messages" "$dir/$list"; fi
}
pass units-doc-default.jsonl
pass units-doc.jsonl --all-features
