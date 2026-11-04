#!/usr/bin/env bash
# Prints the package arguments the Rust checks of `mise run check` take for
# the change in this worktree (#5014, `packages.jq`), on one line: the whole
# workspace, `--workspace` alone, or the workspace with every package outside
# the change's set excluded. The set is each package the change touches and
# each package that depends on one. An exclusion, not a `--package` list,
# because `cargo test --doc` refuses a named package without a library and
# passes over one under `--workspace`. The packages it runs over are named on
# stderr. The change is read as `select.bash` reads it. Without `origin/main`
# the change is unknown, and the scope is the whole workspace. A change with
# no Rust path selects no Rust check, and its scope is the whole workspace
# too, so a Rust check run by hand never excludes every package.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
root=$(git rev-parse --show-toplevel)
if ! base=$(git merge-base origin/main HEAD 2> /dev/null); then
  echo "scope: no fork from origin/main to read the change against; the whole workspace" >&2
  echo --workspace
  exit 0
fi
changed=$({ git diff --no-renames --name-only "$base"; git ls-files --others --exclude-standard; } | jq -R . | jq -cs .)
packages=$(cargo metadata --format-version 1 --no-deps --locked --manifest-path "$root/Cargo.toml" \
  | jq -c --arg root "$root/" '[.packages[] | {name, dir: (.manifest_path | ltrimstr($root) | rtrimstr("/Cargo.toml")), deps: [.dependencies[].name]}]')
set=$(jq -n --argjson changed "$changed" --argjson packages "$packages" '{changed: $changed, packages: $packages}' \
  | jq -c -L "$here" -f "$here/packages.jq")
jq -r --argjson packages "$packages" \
  'if . == "workspace" then "scope: the whole workspace"
   elif length == 0 then "scope: no Rust path changes; a Rust check run by hand runs over the whole workspace"
   else "scope: \(length) of \($packages | length) packages: \(join(" "))" end' <<< "$set" >&2
jq -r --argjson packages "$packages" \
  'if . == "workspace" or length == 0 then "--workspace"
   else . as $set | ["--workspace"] + [$packages[].name | select(IN($set[]) | not) | "--exclude " + .] | join(" ") end' <<< "$set"
