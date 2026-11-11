#!/usr/bin/env bash
# The head watcher's setting reaches no case of the gate (#6739), run by
# `check:integration`. The watcher's whole-suite setting once reached
# `.config/gate-scope/tests-cases.bash`, so `check:gate-scope` failed on every
# head, the green head too, and the watcher filed nothing. Every gate now
# runs the whole suite (#6738), and the watcher sets only
# `GANDR_GATE_BACKGROUND`. The case runs `check:gate-scope` on this checkout,
# a green head, as the watcher's gate runs it and as a lane's gate runs it,
# and reads the failed checks of each log as the watcher reads them
# (`watch_failed`).
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-watch-environment.XXXXXX")
trap 'rm -rf "$work"' EXIT
export XDG_STATE_HOME=$work/state
# shellcheck source=watch.bash
source "$here/watch.bash"
failed=0
fail() {
  echo "watch-environment case FAILED: $1"
  echo "  got: $2"
  failed=1
}

# The failed checks of `check:gate-scope` on this checkout, one per line,
# with `GANDR_GATE_BACKGROUND` set to `$1`, or unset when `$1` is empty.
reading() {
  if [[ -n $1 ]]; then
    GANDR_GATE_BACKGROUND=$1 mise run check:gate-scope > "$work/log" 2>&1 || :
  else
    env -u GANDR_GATE_BACKGROUND mise run check:gate-scope > "$work/log" 2>&1 || :
  fi
  watch_failed "$work/log"
}

got=$(reading 1)
[[ -z $got ]] || fail "#6739: no case of the gate reads the watcher's setting from its caller, so the watcher's gate of a green head reads no red check" "$got"

got=$(reading '')
[[ -z $got ]] || fail "#6739: a lane's gate of a green head reads no red check of check:gate-scope" "$got"

(( failed == 0 )) || exit 1
echo "watch-environment check OK: check:gate-scope on a green head reads no red check as the watcher's gate and as a lane's gate run it"
