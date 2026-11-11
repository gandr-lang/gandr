#!/usr/bin/env bash
# shellcheck disable=SC2154 # watch.bash, sourced below, sets watch_tree
# The head watcher reads the newest head of `landing` before it searches a
# red check (#6679), run by `check:integration`. Each case sources the real
# script over a scratch state directory and a scratch clone. The gate on the
# head fails in `check:a`, and the fetch moves `landing` past the head when
# the case asks it to. The stub of the check reads the newest head as green
# or red, and the stub of the search records that it runs.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-watch-repaired.XXXXXX")
trap 'rm -rf "$work"' EXIT
export XDG_STATE_HOME=$work/state
# shellcheck source=watch.bash
source "$here/watch.bash"
failed=0
fail() {
  echo "watch-repaired case FAILED: $1"
  echo "  got: $2"
  failed=1
}
git() { command git -c user.name=case -c user.email=case@example.invalid -c commit.gpgsign=false "$@"; }
git init --quiet "$watch_tree"
git -C "$watch_tree" commit --quiet --allow-empty -m main
git -C "$watch_tree" update-ref refs/watch/main HEAD
git -C "$watch_tree" commit --quiet --allow-empty -m red
red=$(git -C "$watch_tree" rev-parse HEAD)
git -C "$watch_tree" commit --quiet --allow-empty -m repaired
repaired=$(git -C "$watch_tree" rev-parse HEAD)
watch_gap() { printf '%s\n' '{"minutes":0,"page":false,"coordinator":false,"line":"no gap"}'; }
watch_token() { :; }
watch_failed() { echo check:a; }
watch_own() { echo search >> "$work/acts"; }
# The first fetch reads the red head; a later one reads `$moved`.
watch_fetch() {
  if [[ -e $work/fetched ]]; then
    git -C "$watch_tree" update-ref refs/watch/landing "$moved"
  else
    : > "$work/fetched"
    git -C "$watch_tree" update-ref refs/watch/landing "$red"
  fi
}
# The gate fails on the red head; the check gives `$newest_check` elsewhere.
watch_run() {
  if [[ $2 == check ]]; then return 1; fi
  echo "check $2 on $(git -C "$watch_tree" rev-parse --short "$1")" >> "$work/acts"
  [[ $newest_check == green ]]
}
# One reading: `$1` is the head that the later fetch reads, `$2` the check
# on it. Prints the acts of the reading and its log line, one per line.
reading() {
  moved=$1 newest_check=$2
  rm -f "$work/fetched" "$work/acts" "$work/err"
  watch_remember '{}'
  watch_once case/case > /dev/null 2> "$work/err"
  cat "$work/acts" 2> /dev/null || :
  grep -o 'no search' "$work/err" || :
}
short=$(git -C "$watch_tree" rev-parse --short "$repaired")

got=$(reading "$repaired" green | paste -sd ' ' -)
[[ $got == "check check:a on $short no search" ]] || fail "#6679: a red check that a newer head of landing holds green runs no search" "$got"

got=$(reading "$repaired" red | paste -sd ' ' -)
[[ $got == "check check:a on $short search" ]] || fail "#6679: a red check that the newest head of landing holds red runs the search" "$got"

got=$(reading "$red" green | paste -sd ' ' -)
[[ $got == "search" ]] || fail "#6679: a red check on a head that landing has not passed runs the search, with no check on the newest head" "$got"

(( failed == 0 )) || exit 1
echo "watch-repaired check OK: a red that a newer head holds green runs no search, and a red there or an unmoved head runs it"
