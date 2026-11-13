#!/usr/bin/env bash
# What a change builds that a consumer sees, and where the body says that the
# consumer sees it (#6873): the `views` reading of `pr:open` (`opening.jq`).
#
# Usage: views.bash <base> <body>
#
# It prints one JSON object, `{built, tests}`. `built` names each request
# `gandr/<name>` that a dispatch arm under `crates/surface-lsp*/src` serves at
# HEAD and not at the base. It also names each card type, a
# `pub struct <Name>Card` under `crates/surface-render-remote/src`, that HEAD
# adds. `tests` holds one `{surface, test, found}` for each row of the body's
# `## Observed at` that names a shipped surface (`views.jq`). `found` is true
# when the test stands at HEAD under the paths of the surface
# (`surfaces.json`). A Rust test stands as `fn <name>`, where `<name>` is the
# last segment of the cell's path. A test of the extension stands as its
# `test(…)` call, the cell's text quoted in it.
set -euo pipefail
export LC_ALL=C
claims=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
base=${1:?usage: views.bash <base> <body>}
body=${2:?usage: views.bash <base> <body>}

# The requests that the dispatch arms serve at commit $1, one for each line.
requests() {
  { git grep -h -o -E '"gandr/[A-Za-z]+"\)[[:space:]]*=>' "$1" -- ':(glob)crates/surface-lsp*/src/**' || true; } \
    | awk -F'"' '{ print $2 }' | sort -u
}

# The card types at commit $1, one for each line.
cards() {
  { git grep -h -o -E 'pub struct [A-Za-z0-9_]+' "$1" -- ':(glob)crates/surface-render-remote/src/**' || true; } \
    | awk '$3 ~ /Card$/ { print $3 }' | sort -u
}

built=$({
  comm -13 <(requests "$base") <(requests HEAD) | awk '{ print "request `" $0 "`" }'
  comm -13 <(cards "$base") <(cards HEAD) | awk '{ print "card `" $0 "`" }'
} | jq -R . | jq -s -c .)

# Whether `git grep` finds the arguments `$@` at HEAD under the paths of the
# row's surface. Each path of `surfaces.json` lies under `contrib/` or
# `crates/`, the directories that the reads row of `check:claims` names for
# this search (`.config/gate-scope/table.json`, #6895). The search reads each
# directory as the tree `HEAD:<directory>/`, with the surface's paths below
# it. A path outside both is refused by name.
stands() {
  local path
  local -a contrib=() crates=()
  for path in "${paths[@]}"; do
    case $path in
      contrib/*) contrib+=("${path#contrib/}") ;;
      crates/*) crates+=("${path#crates/}") ;;
      *) echo "views: the surface $surface names $path, outside contrib/ and crates/" >&2; exit 2 ;;
    esac
  done
  { (( ${#contrib[@]} > 0 )) && git grep -q "$@" HEAD:contrib/ -- "${contrib[@]}"; } \
    || { (( ${#crates[@]} > 0 )) && git grep -q "$@" HEAD:crates/ -- "${crates[@]}"; }
}

tests=$(jq -R -s -c -L "$claims" 'include "views"; observed_tests' "$body" \
  | while IFS= read -r row; do
    surface=$(jq -r .surface <<< "$row")
    cell=$(jq -r .test <<< "$row")
    mapfile -t paths < <(jq -r --arg surface "$surface" '.[] | select(.surface == $surface) | .paths[]' "$claims/surfaces.json")
    name=${cell##*::}
    found=false
    if [[ $name =~ ^[A-Za-z_][A-Za-z0-9_]*$ ]] && stands -E "fn ${name}[[:space:]]*[(<]"; then
      found=true
    elif [[ -n $cell ]] && stands -F -e "test(\"$cell\"" -e "test('$cell'" -e "test(\`$cell\`"; then
      found=true
    fi
    jq -c --argjson found "$found" '. + {found: $found}' <<< "$row"
  done | jq -s -c .)

# The lists are of unbounded size, so they reach jq as files (#7091).
jq -n -c --slurpfile built <(printf '%s\n' "$built") --slurpfile tests <(printf '%s\n' "$tests") \
  '{built: $built[0], tests: $tests[0]}'
