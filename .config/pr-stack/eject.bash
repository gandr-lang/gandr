#!/usr/bin/env bash
# The cases of the ejection that `pr:open` and `pr:land` run.
# `check:pr-stack` runs each case of `eject.json`.
# - see: #8225, `stack_eject`
#
# Each case makes a scratch repository with a local bare origin. Its stack
# is `a`, `b`, `c`, bottom to top, and each member holds one commit of its
# own. The pull requests are 2 for `a`, 3 for `b` and 4 for `c`, in the
# server stack 9.
#
# A case names each member that is red, a draft, in conflict or queued. Its
# `builds` names a member whose commit writes the file of the member below
# it again. Then the function cannot replay that member past the one below.
#
# The harness records each call of `gh`, `stack_link` and `page_left` and
# runs none of them. The server takes each edit.
#
# The result is one line, which the harness compares with the `output` of
# the case. It holds the lines of the ejection first. Then it holds the
# subjects that each branch holds past `main`, the `gh` calls, each chain
# that the tool links, and each page. The text `, waits` follows the lines
# of an ejection that returns 1.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
source "$here/stack.bash"
cases=$here/eject.json
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-eject.XXXXXX")
trap 'rm -rf "$work"' EXIT
export GANDR_HOST_LOCK_DIR=$work
repo=case/case
trunk=main
failed=0

source "$here/../cases/scratch.bash"
subjects() { git log --format=%s "origin/main..origin/$1" | paste -sd ',' - | sed 's/,/, /g'; }

# The scratch stack in `$1`. `$2` is the member whose commit rewrites the file
# of the member below it, or `none`.
scenario() {
  git init --quiet --bare --initial-branch=main "$1/origin.git"
  git clone --quiet "$1/origin.git" "$1/clone" 2> /dev/null
  cd "$1/clone"
  identity
  commit base.txt base base
  git push --quiet origin main
  git switch --quiet --create a
  commit a.txt a "a's own"
  git switch --quiet --create b
  if [[ $2 == 3 ]]; then commit a.txt b "b's own"; else commit b.txt b "b's own"; fi
  git switch --quiet --create c
  if [[ $2 == 4 ]]; then commit b.txt c "c's own"; else commit c.txt c "c's own"; fi
  git push --quiet origin a b c
}

count=$(jq length "$cases")
for (( i = 0; i < count; i++ )); do
  name=$(jq -r ".[$i].name" "$cases")
  expected=$(jq -r ".[$i].output" "$cases")
  case_json=$(jq -c ".[$i]" "$cases")
  dir=$work/$i
  mkdir "$dir"
  scenario "$dir" "$(jq -r '.builds // "none"' <<< "$case_json")"
  cd "$dir/clone"
  : > "$dir/gh"
  : > "$dir/link"
  : > "$dir/page"
  gh() {
    case "$*" in
      "api repos/case/case/actions/runs?status="*) ;;
      "pr comment "*) printf 'pr comment %s\n' "$3" >> "$dir/gh" ;;
      *) printf '%s\n' "$*" >> "$dir/gh" ;;
    esac
  }
  red_reading() {
    if [[ $(jq --argjson n "$1" '(.red // []) | index($n) != null' <<< "$case_json") == true ]]; then
      jq -cn '{check: "test the workspace", run: "https://example.invalid/runs/1"}'
    else
      echo null
    fi
  }
  required_contexts() { echo '[]'; }
  members_json='[{"number":2,"head":"a","base":"main"},{"number":3,"head":"b","base":"a"},{"number":4,"head":"c","base":"b"}]'
  open_prs() { printf '%s\n' "$members_json"; }
  pulls_reading() {
    jq -c --argjson case "$case_json" 'map(.number as $n | {number, headRefName: .head, labels: {nodes: []}, autoMergeRequest: null,
      isDraft: (($case.draft // []) | index($n) != null),
      isInMergeQueue: (($case.queued // []) | index($n) != null),
      mergeable: (if ($case.conflicting // []) | index($n) != null then "CONFLICTING" else "MERGEABLE" end)})' <<< "$members_json"
  }
  queued_of() { jq -c '.queued // []' <<< "$case_json"; }
  stack_of() { if grep -q '^stack unstack' "$dir/gh"; then echo null; else echo 9; fi; }
  pr_reading() { jq -n -c --arg base "$(sed -n "s/^pr edit $1 .* --base //p" "$dir/gh" | tail -n 1)" '{baseRefName: $base}'; }
  stack_link() { jq -r 'map(.number) | join(" ")' <<< "$1" >> "$dir/link"; }
  page_left() { printf '#%s [%s] %s\n' "$1" "$2" "$3" >> "$dir/page"; }
  status=0
  lines=$(stack_eject "$members_json" 2> "$dir/out") || status=$?
  actual="eject: $(paste -sd '|' <<< "$lines" | sed 's/|/ | /g')"
  (( status == 0 )) || actual+=", waits"
  git fetch --quiet origin
  actual+="; a holds $(subjects a); b holds $(subjects b); c holds $(subjects c)"
  actual+="; gh: $(paste -sd '|' "$dir/gh" | sed 's/|/ | /g'); link: $(paste -sd '|' "$dir/link" | sed 's/|/ | /g'); page: $(paste -sd '|' "$dir/page" | sed 's/|/ | /g')"
  cd - > /dev/null
  if [[ $actual != "$expected" ]]; then
    printf 'pr-stack eject case %s\n  expected: %s\n  actual:   %s\n' "$name" "$expected" "$actual" >&2
    sed 's/^/    /' "$dir/out" >&2
    failed=1
  fi
done
(( failed == 0 )) || exit 1
echo "pr-stack eject OK: $count cases take each member that cannot land out of its stack as recorded"
