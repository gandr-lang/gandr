#!/usr/bin/env bash
# Prints the package arguments the Rust checks of `mise run check` take for
# the change in this worktree (#5014, `packages.jq`), on one line: the whole
# workspace, `--workspace` alone, or the workspace with every package outside
# the change's set excluded. The set is each package the change touches and
# each package that depends on one. An exclusion, not a `--package` list,
# because `cargo test --doc` refuses a named package without a library and
# passes over one under `--workspace`. The packages it runs over are named on
# stderr. The change is read as `select.bash` reads it, against `GATE_BASE`
# when it names a commit: the queue of `landing` names the group's base
# there (#6894). Else the change runs from the fork from the trunk
# (`.config/pr-stack/trunk.bash`). Without either the change is unknown, and
# the scope is the whole workspace. A change with no Rust path selects no
# Rust check, and its scope is the whole workspace too, so a Rust check run by
# hand never excludes every package. With `--touched`, the set is the
# packages the change touches alone, for `check:witnesses` (#6433). With
# `--readers`, the set holds the packages whose tests read the corpus and the
# whole pipeline too (`table.json`'s `readers`), for a lane's enforcing suite
# (#6812). With `--lints`, a change of a lint's configuration reads the whole
# workspace (`table.json`'s `lints`), for the lints of the queue (#6894).
#
# Usage: scope.bash [--touched] [--readers] [--lints]
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
root=$(git rev-parse --show-toplevel)
source "$here/../pr-stack/trunk.bash"
touched=false
readers=false
lints=false
for arg in "$@"; do
  case $arg in
    --touched) touched=true ;;
    --readers) readers=true ;;
    --lints) lints=true ;;
    *) echo "scope: unknown argument $arg; usage: scope.bash [--touched] [--readers] [--lints]" >&2; exit 2 ;;
  esac
done
if [[ -n ${GATE_BASE:-} ]]; then
  if ! git cat-file -e "$GATE_BASE^{commit}" 2> /dev/null; then
    git fetch --quiet --no-tags --depth=1 origin "$GATE_BASE"
  fi
  base=$GATE_BASE
elif ! base=$(git merge-base "origin/$trunk" HEAD 2> /dev/null); then
  echo "scope: no fork from origin/$trunk to read the change against; the whole workspace" >&2
  echo --workspace
  exit 0
fi
packages=$(cargo metadata --format-version 1 --no-deps --locked --manifest-path "$root/Cargo.toml" \
  | jq -c --arg root "$root/" '[.packages[] | {name, dir: (.manifest_path | ltrimstr($root) | rtrimstr("/Cargo.toml")), deps: [.dependencies[].name]}]')
# The change goes to `jq` on stdin, as `select.bash` reads it: one argument
# holds at most 128 KiB, and a change of many paths holds more.
set=$({ git diff --no-renames --name-only "$base"; git ls-files --others --exclude-standard; } \
  | jq -nR --argjson packages "$packages" --argjson touched "$touched" --argjson lints "$lints" '{changed: [inputs], packages: $packages, touched: $touched, lints: $lints}' \
  | jq -c -L "$here" -f "$here/packages.jq")
if [[ $readers == true ]]; then
  set=$(jq -c --slurpfile table "$here/table.json" 'if . == "workspace" then . else . + $table[0].readers | unique end' <<< "$set")
fi
jq -r --argjson packages "$packages" \
  'if . == "workspace" then "scope: the whole workspace"
   elif length == 0 then "scope: no Rust path changes; a Rust check run by hand runs over the whole workspace"
   else "scope: \(length) of \($packages | length) packages: \(join(" "))" end' <<< "$set" >&2
jq -r --argjson packages "$packages" \
  'if . == "workspace" or length == 0 then "--workspace"
   else . as $set | ["--workspace"] + [$packages[].name | select(IN($set[]) | not) | "--exclude " + .] | join(" ") end' <<< "$set"
