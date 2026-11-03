#!/usr/bin/env bash
# `pr:watch`'s heal, run by `check:pr-stack` over the cases in `heal.json`
# under `set -u`, as the task runs it (#4766). The heal is read from the task
# itself. The stack holds pull requests 2, 3 and 4, and the watch is on 3.
# A case's `red` names the member a required check failed on, or is null.
# The server, the fetch and the restacks are recorded, not run. The result is
# one line compared with the case's `output`: the heal's status, the restack
# it asked for, and its `pr-restacked` report. The globals each case sets are
# the ones the heal reads.
# shellcheck disable=SC2034
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
tasks=$here/../mise/tasks/mise-tasks-ci.toml
cases=$here/heal.json
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-heal.XXXXXX")
trap 'rm -rf "$work"' EXIT
yq -p toml -o yaml '."pr:watch".run' "$tasks" | awk '/^heal\(\) \{/,/^\}$/' > "$work/heal"
[[ -s "$work/heal" ]] || { echo "pr-stack heal: no heal() in pr:watch" >&2; exit 1; }
# shellcheck source=/dev/null
source "$work/heal"
failed=0

members_json='[{"number":2,"head":"lower"},{"number":3,"head":"own"},{"number":4,"head":"top"}]'
server_stack() { printf '%s\n' "$members_json"; }
queued_of() { echo '[]'; }
queue_removal() { echo none; }
member_paths() { echo '[]'; }
git() { :; }
restack() { jq -r '"restack " + (map("#\(.number)") | join(" "))' <<< "$1" > "$work/asked"; }
restack_past() { echo "past #$2" > "$work/asked"; }

count=$(jq length "$cases")
for (( i = 0; i < count; i++ )); do
  name=$(jq -r ".[$i].name" "$cases")
  expected=$(jq -r ".[$i].output" "$cases")
  red_member=$(jq -r ".[$i].red // empty" "$cases")
  red_check() { if [[ $1 == "$red_member" ]]; then echo required; fi; }
  number=3
  heals=0
  waited=
  trunk=main
  pr_stack_dir=$here
  : > "$work/asked"
  status=0
  (heal) 2> "$work/err" || status=$?
  report=$(grep -E '^pr-restacked ' "$work/err" || true)
  actual="status $status; $(< "$work/asked"); ${report:-no report}"
  if [[ $actual != "$expected" ]]; then
    printf 'pr-stack heal case %s\n  expected: %s\n  actual:   %s\n' "$name" "$expected" "$actual" >&2
    sed 's/^/    /' "$work/err" >&2
    failed=1
  fi
done
(( failed == 0 )) || exit 1
echo "pr-stack heal OK: $count cases heal as recorded"
