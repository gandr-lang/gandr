#!/usr/bin/env bash
# The stacking step over a top that lacks a trunk change (#3654), run by
# `check:pr-stack` over the cases in `behind.json`. Each case builds a scratch
# repository with a local bare origin: a base commit, a lower branch with one
# commit of its own, the trunk's change `trunk B` to `f.txt`, and an upper
# branch whose own commit edits that line again. The case says:
# - `top`: `behind` forks the lower from the base, before `trunk B`;
#   `current` forks it from the trunk after `trunk B`.
# - `lower`: `apart` has the lower edit another file; `clashes` has it edit
#   `f.txt` too.
# - `reading`: what `top_reading` reads for the lower (`bound.jq`'s input).
# - `restacked` (#3877): the upper is stacked on the lower once, and the
#   lower's own commit is then rewritten with another patch and pushed, as
#   its seat's restack does, before the step runs.
# The server is stubbed: no other pull request is open, and the top read
# after a wait is `null`, the lower having merged. The result is one line
# compared with the case's `output`: `stacked on <branch>`, with `, waited`
# when the step waited, or `refused: <why>`.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
source "$here/stack.bash"
cases=$here/behind.json
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-behind-top.XXXXXX")
trap 'rm -rf "$work"' EXIT
repo=case/case
trunk=main
pr_stack_poll=0
failed=0

commit() { printf '%s\n' "$2" > "$1" && git add "$1" && git commit --quiet --message "$3"; }

# The scratch repository in `$1`, its lower forked as `$2` and edited as `$3`.
scenario() {
  git init --quiet --bare --initial-branch=main "$1/origin.git"
  git clone --quiet "$1/origin.git" "$1/clone" 2> /dev/null
  cd "$1/clone"
  git config user.name case
  git config user.email case@example.invalid
  git config commit.gpgsign false
  commit f.txt a base
  git push --quiet origin main
  if [[ $2 == behind ]]; then git switch --quiet --create lower; fi
  if [[ $2 == current ]]; then
    commit f.txt b 'trunk B'
    git push --quiet origin main
    git switch --quiet --create lower
  fi
  if [[ $3 == clashes ]]; then commit f.txt x "lower's own"; else commit l.txt l "lower's own"; fi
  git push --quiet origin lower
  git switch --quiet main
  if [[ $2 == behind ]]; then
    commit f.txt b 'trunk B'
    git push --quiet origin main
  fi
  git switch --quiet --create upper
  commit f.txt c "upper's own"
  git fetch --quiet origin
}

count=$(jq length "$cases")
for (( i = 0; i < count; i++ )); do
  name=$(jq -r ".[$i].name" "$cases")
  expected=$(jq -r ".[$i].output" "$cases")
  reading=$(jq -c ".[$i].reading" "$cases")
  dir=$work/$i
  mkdir "$dir"
  ( scenario "$dir" "$(jq -r ".[$i].top" "$cases")" "$(jq -r ".[$i].lower" "$cases")" ) > /dev/null
  cd "$dir/clone"
  open_prs() { echo '[]'; }
  top_reading() { echo "$reading"; }
  await_top() { echo null; }
  if [[ $(jq -r ".[$i].restacked // false" "$cases") == true ]]; then
    stack_on_top upper '{"number":1,"head":"lower"}' > "$dir/out" 2>&1
    (
      git clone --quiet --branch lower "$dir/origin.git" "$dir/seat" 2> /dev/null
      cd "$dir/seat"
      git config user.name case
      git config user.email case@example.invalid
      git config commit.gpgsign false
      printf '%s\n' restacked > l.txt
      git commit --quiet --all --amend --no-edit
      git push --quiet --force origin lower
    ) > /dev/null
    git fetch --quiet origin
  fi
  if stack_on_top upper '{"number":1,"head":"lower"}' > "$dir/out" 2>&1; then
    if [[ $stacked_top == null ]]; then actual="stacked on main"; else actual="stacked on $(jq -r .head <<< "$stacked_top")"; fi
    if grep -q 'waiting for it to merge' "$dir/out"; then actual+=", waited"; fi
  else
    actual="refused: $(grep -o -E 'lacks these changes[^;]*|conflicts; resolve' "$dir/out" | head -n 1 || true)"
    if grep -q -F 'trunk B' "$dir/out"; then actual+=" (names trunk B)"; fi
  fi
  cd - > /dev/null
  if [[ $actual != "$expected" ]]; then
    printf 'pr-stack behind-top case %s\n  expected: %s\n  actual:   %s\n' "$name" "$expected" "$actual" >&2
    sed 's/^/    /' "$dir/out" >&2
    failed=1
  fi
done
(( failed == 0 )) || exit 1
echo "pr-stack behind-top OK: $count cases stack as recorded"
