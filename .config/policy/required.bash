#!/usr/bin/env bash
# The features that the targets of the workspace's packages require, read
# from `cargo metadata --no-deps` on stdin. A lint run turns them on, so a
# target that builds only with a feature, as a report or a bench, is built
# and linted too.
#
#   required.bash --package <name>   the features of one package, joined by
#                                    commas, or nothing
#   required.bash <scope>...         `--features` and each feature of each
#                                    package that the scope keeps, as
#                                    `<package>/<feature>`, or nothing
#
# A scope is the `GATE_SCOPE` form: `--workspace` with `--exclude <name>`,
# or `-p <name>` and `--package <name>`.
set -euo pipefail

# A failed `cargo metadata` gives no input, and a run without its features
# would pass unseen, so the script refuses it.
metadata=$(cat)
[[ -n $metadata ]] || { echo "required.bash: no metadata on stdin" >&2; exit 2; }

if [[ ${1:-} == --package ]]; then
  jq -r --arg name "${2:?usage: required.bash --package <name>}" \
    '[.packages[] | select(.name == $name) | .targets[] | .["required-features"][]?] | unique | join(",")' <<< "$metadata"
  exit 0
fi

all=false
excluded=()
selected=()
while (( $# )); do
  case $1 in
    --workspace) all=true ;;
    --exclude) excluded+=("${2:?--exclude takes a package}"); shift ;;
    -p | --package) selected+=("${2:?$1 takes a package}"); shift ;;
    *) echo "required.bash: $1 is no part of a scope" >&2; exit 2 ;;
  esac
  shift
done
jq -r --argjson all "$all" \
  --argjson excluded "$(jq -n '$ARGS.positional' --args "${excluded[@]}")" \
  --argjson selected "$(jq -n '$ARGS.positional' --args "${selected[@]}")" '
  [.packages[]
    | select(($all and (.name | IN($excluded[]) | not)) or (.name | IN($selected[])))
    | .name as $package
    | [.targets[] | .["required-features"][]?] | unique[]
    | "\($package)/\(.)"]
  | if length > 0 then "--features " + join(",") else empty end' <<< "$metadata"
