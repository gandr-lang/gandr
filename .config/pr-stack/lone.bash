#!/usr/bin/env bash
# The hold of `land_prefix` on a pull request whose checks still run, run by
# `check:pr-stack` over the cases in `lone.json`. Each case gives the stack
# bottom to top, the state of each member, and the server stack of each
# member. The harness records `gh`, `queue_stack` and the readings of the
# server, and runs none of them. The result is one line compared with the
# case's `output`: the status of `land_prefix`, its last line on stderr,
# `prefix_auto`, and the calls.
# - see: #7801
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
source "$here/stack.bash"
cases=$here/lone.json
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-lone.XXXXXX")
trap 'rm -rf "$work"' EXIT
repo=case/case
trunk=main
failed=0

count=$(jq length "$cases")
for (( i = 0; i < count; i++ )); do
  name=$(jq -r ".[$i].name" "$cases")
  expected=$(jq -r ".[$i].output" "$cases")
  # `land_prefix` holds locals named `states` and `server`, so the case's
  # readings take names of their own.
  case_stack=$(jq -c ".[$i].stack" "$cases")
  case_states=$(jq -c ".[$i].states" "$cases")
  case_servers=$(jq -c ".[$i].stacks" "$cases")
  : > "$work/calls"
  git() { :; }
  gh() { printf '%s\n' "$*" >> "$work/calls"; }
  open_prs() { echo '[]'; }
  server_stack() { echo "$case_stack"; }
  queued_of() { echo '[]'; }
  rewritten_fork() { :; }
  carried_queued() { echo '[]'; }
  required_contexts() { echo '[]'; }
  queue_unit_cap() { echo 0; }
  required_state() { jq -r --arg n "$1" '.[$n]' <<< "$case_states"; }
  stack_of() { jq -r --arg n "$1" '.[$n] // "null"' <<< "$case_servers"; }
  hold_landing() { printf 'hold %s\n' "$1" >> "$work/calls"; }
  release_landing() { printf 'release\n' >> "$work/calls"; }
  queue_stack() { printf 'queue up to %s\n' "$3" >> "$work/calls"; }
  status=0
  land_prefix "$(jq -r '.[-1].number' <<< "$case_stack")" 2> "$work/out" || status=$?
  actual="status $status; $(awk 'NF { line = $0 } END { print line }' "$work/out"); auto ${prefix_auto:-none}"
  actual+="; calls: $(paste -sd '|' "$work/calls" | sed 's/|/ | /g')"
  if [[ $actual != "$expected" ]]; then
    printf 'pr-stack lone case %s\n  expected: %s\n  actual:   %s\n' "$name" "$expected" "$actual" >&2
    sed 's/^/    /' "$work/out" >&2
    failed=1
  fi
done
(( failed == 0 )) || exit 1
echo "pr-stack lone OK: $count cases set auto-merge only on a lone pull request whose checks still run"
