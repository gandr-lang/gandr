#!/usr/bin/env bash
# The `gh` call sites a change alters (#5061), read by `pr:open` and handed
# to `opening.jq`'s `budget`:
#
#   changed.bash <base> [head]
#
# Prints a JSON array of `{file, scope, api}`, sorted and once each. A site
# is altered when its calls of one API differ between <base> and <head>,
# `HEAD` by default, in verb or in text, as `sites.awk -v text=1` lists
# them, so a query that asks for more nodes is altered too. A site is
# altered as well when its rows in `calls.toml` differ, or when the change
# adds or removes it. A base with no `calls.toml` gives no rows, so only
# the calls count then.
set -euo pipefail
base=${1:?usage: changed.bash <base> [head]}
head=${2:-HEAD}
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
table=.config/gh/calls.toml
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
mapfile -t touched < <(git diff --no-renames --name-only "$base" "$head" -- \
  '.config/*.sh' '.config/*.bash' '.config/*.toml' '.github/*.yml' '.github/*.yaml')

# One revision's calls in the touched files, as `[{file, scope, api, verb, text}]`.
calls() {
  local rev=$1 dir=$work/$1
  local -a present=()
  mkdir -p "$dir"
  if ((${#touched[@]} > 0)); then
    mapfile -t present < <(git ls-tree -r --name-only "$rev" -- "${touched[@]}")
  fi
  if ((${#present[@]} > 0)); then
    git archive "$rev" -- "${present[@]}" | tar -x -C "$dir"
    (cd "$dir" && awk -v text=1 -f "$here/sites.awk" "${present[@]}")
  fi | jq -R -s -c -L "$here" 'include "class";
    split("\n") | map(select(. != "") | split("\t") | {file: .[0], scope: .[1], verb: .[2], text: .[3]} | . + {api: (.verb | class | .api)})'
}

# One revision's rows, or none when the revision has no table.
rows() {
  if git cat-file -e "$1:$table" 2> /dev/null; then
    git show "$1:$table" | yq -p toml -o json -I 0 '.site // []'
  else
    echo '[]'
  fi
}

jq -n -c --argjson was "$(calls "$base")" --argjson now "$(calls "$head")" \
  --argjson rows_was "$(rows "$base")" --argjson rows_now "$(rows "$head")" '
  def site: {file, scope, api};
  def by_site: group_by([.file, .scope, .api]) | map({key: (.[0] | site | tojson), value: .}) | from_entries;
  def altered($a; $b): ($a | by_site) as $x | ($b | by_site) as $y
    | [($x + $y | keys[]) | select(($x[.] // [] | map(del(.file, .scope, .api) | tojson) | sort) != ($y[.] // [] | map(del(.file, .scope, .api) | tojson) | sort)) | fromjson];
  if ($rows_was | length) == 0 then [] else altered($rows_was; $rows_now) end as $priced
  | altered($was; $now) + $priced
  | unique'
