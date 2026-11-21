#!/usr/bin/env bash
# The stack merge above queued members (#4843), run by `check:pr-stack` over
# the cases in `queue.json`. Each case gives a stack bottom to top, the
# members already queued, the member to queue up to, and the server stack
# each member belongs to. `gh` is recorded, not run, and a `gh stack link`
# puts each pull request it names in stack 9, as the server would; the
# retargeting, the required checks and the twin runs `queue_stack` reads are
# stubbed, and `stack_link` and `link.jq` run as written. A case's `foreign`
# is the reading of the lowest open member's branch (`foreign_commits`,
# #6797), empty when absent. The result is one line compared with the case's
# `output`: `queue_stack`'s exit status, then the `gh` calls it made.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
source "$here/stack.bash"
cases=$here/queue.json
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-queue.XXXXXX")
trap 'rm -rf "$work"' EXIT
repo=case/case
trunk=main
failed=0

count=$(jq length "$cases")
for (( i = 0; i < count; i++ )); do
  name=$(jq -r ".[$i].name" "$cases")
  expected=$(jq -r ".[$i].output" "$cases")
  servers=$(jq -c ".[$i].stacks" "$cases")
  : > "$work/gh"
  gh() {
    printf '%s\n' "$*" >> "$work/gh"
    if [[ $1 == stack && $2 == link ]]; then
      shift 2
      [[ $1 != --base ]] || shift 2
      servers=$(jq -c '. + ($ARGS.positional | map({(.): 9}) | add)' --args "$@" <<< "$servers")
    fi
  }
  stack_of() { jq -r --arg n "$1" '.[$n] // "null"' <<< "$servers"; }
  stack_entries() { echo '[]'; }
  retarget_landing() { :; }
  foreign_commits() { jq -c ".[$i].foreign // []" "$cases"; }
  wait_required() { return 0; }
  rerun_twins() { return 1; }
  status=0
  queue_stack "$(jq -c ".[$i].stack" "$cases")" "$(jq -c ".[$i].queued" "$cases")" "$(jq -r ".[$i].upto" "$cases")" > "$work/out" 2>&1 || status=$?
  actual="status $status; gh: $(paste -sd '|' "$work/gh" | sed 's/|/ | /g')"
  if [[ $actual != "$expected" ]]; then
    printf 'pr-stack queue case %s\n  expected: %s\n  actual:   %s\n' "$name" "$expected" "$actual" >&2
    sed 's/^/    /' "$work/out" >&2
    failed=1
  fi
done
(( failed == 0 )) || exit 1
echo "pr-stack queue OK: $count cases queue above their queued members as recorded"
