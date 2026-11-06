#!/usr/bin/env bash
# `stack_link` reads the entries of each server stack once, whatever the
# number of its members in the chain (#5671), run by `check:pr-stack` over
# the cases in `links.json`. Each case gives the chain, the server stack of
# each member, each stack's entries and the members queued. `gh` is
# recorded, not run. `stack_entries` counts its reads and answers from the
# entries of the member's stack. `stack_of` answers from the servers: after
# an unstack, a member that is not queued leaves its stack, unless the case
# is `stale`, as the host's shared reading of the open pull requests is until
# it reads again. `link.jq` runs as written. The result is one line compared
# with the case's `output`: the entries reads, the stack unstacked, and the
# arguments of `gh stack link`.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
source "$here/stack.bash"
cases=$here/links.json
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-link-reads.XXXXXX")
trap 'rm -rf "$work"' EXIT
repo=case/case
trunk=main
failed=0

gh() {
  printf '%s\n' "$*" >> "$work/gh"
  if [[ $1 == stack && $2 == unstack ]]; then : > "$work/unstacked"; fi
}
stack_of() {
  if [[ -e $work/unstacked && $stale == false ]]; then
    jq -r --arg n "$1" --argjson queued "$queued" 'if ($n | tonumber | IN($queued[])) then (.[$n] // "null") else "null" end' <<< "$servers"
  else
    jq -r --arg n "$1" '.[$n] // "null"' <<< "$servers"
  fi
}
stack_entries() {
  echo "$1" >> "$work/entries"
  jq -c --arg stack "$(jq -r --arg n "$1" '.[$n] // ""' <<< "$servers")" '.[$stack] // []' <<< "$case_entries"
}

count=$(jq length "$cases")
for (( i = 0; i < count; i++ )); do
  name=$(jq -r ".[$i].name" "$cases")
  expected=$(jq -r ".[$i].output" "$cases")
  servers=$(jq -c ".[$i].servers" "$cases")
  case_entries=$(jq -c ".[$i].entries" "$cases")
  queued=$(jq -c ".[$i].queued // []" "$cases")
  stale=$(jq -r ".[$i].stale // false" "$cases")
  rm -f "$work/unstacked"
  : > "$work/gh"
  : > "$work/entries"
  stack_link "$(jq -c ".[$i].chain | map({number: .})" "$cases")"
  unstack=$(sed -n 's/^stack unstack //p' "$work/gh" | paste -sd ' ' -)
  link=$(sed -n 's/^stack link //p' "$work/gh")
  actual="entries $(wc -l < "$work/entries" | tr -d ' '); unstack ${unstack:-none}; link ${link:-none}"
  if [[ $actual != "$expected" ]]; then
    printf 'pr-stack link case %s\n  expected: %s\n  actual:   %s\n' "$name" "$expected" "$actual" >&2
    failed=1
  fi
done
(( failed == 0 )) || exit 1
echo "pr-stack links OK: $count cases read each server stack's entries once"
