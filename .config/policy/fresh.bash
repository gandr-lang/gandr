#!/usr/bin/env bash
# Cargo tracks no record of the base, so a lint result that a run with no
# base leaves stays fresh in a later run with a base (#7640). The lint then
# runs on no unit and holds no changed function. So `check:dylint` runs this
# script after `base-records.bash` and before the policy run.
#
# The script reads the base's records of the run in `<records>` and the stamp
# of the last run in `<stamp>`: one line `<record> <blob>` for each record
# file. A record that is new, gone or of another content names its package,
# and the package leaves each check target of `cargo dylint` under
# `<dylint>/target`. So cargo lints it again against the records of this
# run. A run with the same records keeps its fresh results. Then the stamp
# takes the records of this run, by one `mv`. `cargo dylint` builds a
# workspace that `--manifest-path` names in the check targets of the
# workspace of the caller, so a case cleans those targets with a stamp of its
# own.
#
# A record file belongs to the package whose directory starts its name, as
# `evidence::record_name` forms the name from the path of the unit's root
# file, each character other than a letter, a digit, `_` or `-` as `_`. The
# longest such directory wins.
#
# Usage: fresh.bash <records> <stamp> <dylint> [manifest]
# `[manifest]` is the workspace's `Cargo.toml`, the tree's own by default.
# Prints one line: the count of the packages that lint again, and their names.
set -euo pipefail
usage='usage: fresh.bash <records> <stamp> <dylint> [manifest]'
records=${1:?$usage}
stamp=${2:?$usage}
dylint=${3:?$usage}
manifest=${4:-$(git rev-parse --show-toplevel)/Cargo.toml}
mkdir -p "${stamp%/*}"
next=$(mktemp "$stamp.XXXXXX")
changed=$(mktemp)
trap 'rm -f "$next" "$changed"' EXIT
shopt -s nullglob
files=("$records"/*.jsonl)
shopt -u nullglob
if (( ${#files[@]} )); then
  paste -d ' ' <(printf '%s\n' "${files[@]##*/}") <(git hash-object -- "${files[@]}") | sort > "$next"
fi
comm -3 <(if [[ -f $stamp ]]; then sort "$stamp"; fi) "$next" | awk '{ print $1 }' | sort -u > "$changed"
packages=()
if [[ -s $changed ]]; then
  mapfile -t packages < <(cargo metadata --format-version 1 --no-deps --locked --manifest-path "$manifest" \
    | jq -r --rawfile changed "$changed" '
      (.workspace_root + "/") as $root
      | [.packages[] | {name, prefix: ((.manifest_path | ltrimstr($root) | rtrimstr("/Cargo.toml") | gsub("[^A-Za-z0-9_-]"; "_")) + "_")}] as $packages
      | [$changed | split("\n")[] | select(. != "") as $record
        | [$packages[] | select(.prefix as $prefix | $record | startswith($prefix))] | max_by(.prefix | length) | .name // empty]
      | unique[]')
fi
if (( ${#packages[@]} )); then
  args=()
  for package in "${packages[@]}"; do args+=(-p "$package"); done
  for dir in "$dylint"/target/*/; do
    [[ -d $dir ]] || continue
    cargo clean --quiet --manifest-path "$manifest" "${args[@]}" --target-dir "$dir"
  done
fi
mv "$next" "$stamp"
trap 'rm -f "$changed"' EXIT
echo "fresh: ${#packages[@]} packages lint again, as their base's records change${packages[*]:+: ${packages[*]}}" >&2
