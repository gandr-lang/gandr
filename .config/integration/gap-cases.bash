#!/usr/bin/env bash
# shellcheck disable=SC2154 # watch.bash, sourced below, sets watch_state and watch_tree
# The head watcher writes its gap before the gate (#6675), and each interval
# while the gate runs (#6944), run by `check:integration`. The case sources
# the real script over a scratch state directory and a scratch clone whose
# `landing` moved. The fetch, the gap and the gate are stubs. The gate stub
# reads the state file while it runs, and the case asks it to hold the gap
# of this reading, not the one before.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-watch-gap.XXXXXX")
trap 'rm -rf "$work"' EXIT
export XDG_STATE_HOME=$work/state
# shellcheck source=watch.bash
source "$here/watch.bash"
failed=0
fail() {
  echo "watch-gap case FAILED: $1"
  echo "  got: $2"
  failed=1
}
git() { command git -c user.name=case -c user.email=case@example.invalid -c commit.gpgsign=false "$@"; }
git init --quiet "$watch_tree"
git -C "$watch_tree" commit --quiet --allow-empty -m main
git -C "$watch_tree" update-ref refs/watch/main HEAD
git -C "$watch_tree" commit --quiet --allow-empty -m landing
git -C "$watch_tree" update-ref refs/watch/landing HEAD
watch_remember '{"gap":{"minutes":27,"line":"the gap before"}}'
watch_fetch() { :; }
watch_gap() { printf '%s\n' '{"minutes":3,"page":false,"coordinator":false,"line":"the gap now"}'; }
watch_token() { :; }
watch_run() { jq -r .gap.line "$watch_state" > "$work/seen"; }

watch_once case/case > /dev/null 2>&1
got=$(< "$work/seen")
[[ $got == "the gap now" ]] || fail "#6675: the state holds the gap of the reading before while the gate runs" "$got"

# A gate that runs past three intervals: each interval reads the gap again
# and writes it, and the second reading pages. The gate stub waits for the
# third reading in the state, and the state after the gate keeps the page.
# shellcheck disable=SC2034 # watch_hold, in watch.bash, reads the interval
watch_interval=1
watch_gap() {
  local reads
  echo >> "$work/reads"
  reads=$(wc -l < "$work/reads")
  jq -n -c --argjson n "$reads" '{minutes: $n, page: ($n == 2), coordinator: false, paged: {main: "main \($n)", cycle: null, minutes: $n}, line: "reading \($n)"}'
}
watch_run() {
  local waited
  for ((waited = 0; waited < 30; waited++)); do
    [[ $(jq -r .gap.line "$watch_state") == "reading 3" ]] && break
    sleep 1
  done
  jq -r .gap.line "$watch_state" > "$work/seen"
}
watch_remember '{"gap":{"minutes":27,"line":"the gap before"}}'
state=$(watch_once case/case 2> /dev/null)
got=$(< "$work/seen")
[[ $got == "reading 3" ]] || fail "#6944: the state holds a new gap each interval while the gate runs" "$got"
got=$(jq -c '[.checked == $head, .paged.main]' --arg head "$(git -C "$watch_tree" rev-parse refs/watch/landing)" <<< "$state")
[[ $got == '[true,"main 2"]' ]] || fail "#6944: the state after the gate keeps its head and the page of a reading while it runs" "$got"

(( failed == 0 )) || exit 1
echo "watch-gap check OK: the state holds a reading's gap before its gate runs and each interval while it runs"
