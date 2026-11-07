#!/usr/bin/env bash
# The landing watcher's actions (#5695, `act_on` in `landing.bash`), run by
# `check:pr-stack` over the cases in `watcher.json`. The harness sources
# `landing.bash`, which then runs nothing, and records what an action
# writes. Pull request 5 heads `own` on the base `main`, queued, in server
# stack 9. A case's `action` is the action that `landing.jq` decides. Its
# `restack` is what `signed_restack` gives: `moved`, or `already` when the
# head already stands on its base. Its `landing` is the status of
# `land_prefix` and the last of its lines, and its `retarget` is the same of
# `retarget_bottom` (#5776). The result is one line compared with the case's
# `output`: each comment, its event line and its explanation, the count of
# warnings in the run's log, and the pull request that `retarget_bottom`
# gets, when it runs.
# shellcheck disable=SC2034
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
cases=$here/watcher.json
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-watcher.XXXXXX")
trap 'rm -rf "$work"' EXIT
export GITHUB_REPOSITORY=case/case
# shellcheck source=/dev/null
source "$here/landing.bash"
failed=0

prs='[{"number":5,"oid":"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa","head":"own","base":"main","queued":true,"stack":9}]'
err=$work/err
queued_of() { echo '[]'; }
server_stack() { echo '[]'; }
tell() { printf '%s: %s\n' "$2" "$5" >> "$work/told"; }

count=$(jq length "$cases")
for (( i = 0; i < count; i++ )); do
  name=$(jq -r ".[$i].name" "$cases")
  expected=$(jq -r ".[$i].output" "$cases")
  action=$(jq -c ".[$i].action" "$cases")
  restack=$(jq -r ".[$i].restack // empty" "$cases")
  landing_status=$(jq -r ".[$i].landing.status" "$cases")
  landing_line=$(jq -r ".[$i].landing.line" "$cases")
  retarget_status=$(jq -r ".[$i].retarget.status // 0" "$cases")
  retarget_line=$(jq -r ".[$i].retarget.line // empty" "$cases")
  retarget_bottom() {
    printf '%s\n' "$1" > "$work/retargeted"
    echo "$retarget_line" >&2
    return "$retarget_status"
  }
  signed_restack() { if [[ $restack == moved ]]; then echo bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb; fi; }
  land_prefix() {
    echo "a line before the last" >&2
    echo "$landing_line" >&2
    return "$landing_status"
  }
  : > "$work/told"
  : > "$work/retargeted"
  log=$(act_on "$action" 2>&1)
  warnings=$(grep -c '^::warning::' <<< "$log" || true)
  actual="told: $(paste -sd '|' "$work/told" | sed 's/|/ | /g'); warnings: $warnings"
  if [[ -s $work/retargeted ]]; then actual+="; retargeted: $(< "$work/retargeted")"; fi
  if [[ $actual != "$expected" ]]; then
    printf 'pr-stack watcher case %s\n  expected: %s\n  actual:   %s\n' "$name" "$expected" "$actual" >&2
    sed 's/^/    /' <<< "$log" >&2
    failed=1
  fi
done
(( failed == 0 )) || exit 1
echo "pr-stack watcher OK: $count actions tell their seats as recorded"
