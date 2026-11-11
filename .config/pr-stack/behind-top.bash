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
# The server is stubbed: the lower is the one other open pull request, #1 on
# `main`, queued when its reading is, so a top stacked past leaves the trunk.
# A top behind the trunk and not queued, held or conflicting is restacked
# onto it first (#6760, `restack_behind`), and a stopped restack's page is
# printed. The result is one line compared with the case's `output`:
# `stacked on <branch>`, with `(the top holds main)` or `(the top lacks
# main)` as the origin's lower stands after the step, `, past #<n>` when the
# step stacked past a top, and `, paged` when it paged a stopped restack;
# `armed: <the arm line>` when it waits on the top (#4164); or `refused:
# <why>`.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
source "$here/stack.bash"
cases=$here/behind.json
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-behind-top.XXXXXX")
trap 'drop_scratch; rm -rf "$work"' EXIT
repo=case/case
trunk=main
failed=0
export XDG_CACHE_HOME=$work/cache REPLAY_ARTIFACTS=$work/artifacts.json
echo '[]' > "$REPLAY_ARTIFACTS"

source "$here/../cases/scratch.bash"

# The scratch repository in `$1`, its lower forked as `$2` and edited as `$3`.
scenario() {
  git init --quiet --bare --initial-branch=main "$1/origin.git"
  git clone --quiet "$1/origin.git" "$1/clone" 2> /dev/null
  cd "$1/clone"
  identity
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
  open_prs() { jq -nc --argjson queued "$(jq .queued <<< "$reading")" \
    '[{number: 1, head: "lower", base: "main", created: "2026-11-11T00:00:00Z", landing: $queued, held: false, stack: null, bot: false, hold: null}]'; }
  top_reading() { echo "$reading"; }
  landed_heads() { :; }
  pushed_heads() { :; }
  page_stopped() { sed -n 's/^stopped /paged: stopped /p'; }
  if [[ $(jq -r ".[$i].restacked // false" "$cases") == true ]]; then
    stack_on_top upper '{"number":1,"head":"lower"}' > "$dir/out" 2>&1
    (
      git clone --quiet --branch lower "$dir/origin.git" "$dir/seat" 2> /dev/null
      cd "$dir/seat"
      identity
      printf '%s\n' restacked > l.txt
      git commit --quiet --all --amend --no-edit
      git push --quiet --force origin lower
    ) > /dev/null
    git fetch --quiet origin
  fi
  status=0
  stack_on_top upper '{"number":1,"head":"lower"}' > "$dir/out" 2>&1 || status=$?
  if (( status == 0 )); then
    if [[ $stacked_top == null ]]; then actual="stacked on main"; else actual="stacked on $(jq -r .head <<< "$stacked_top")"; fi
    if [[ $stacked_top != null ]]; then
      if git merge-base --is-ancestor origin/main origin/lower; then actual+=" (the top holds main)"; else actual+=" (the top lacks main)"; fi
    fi
    if [[ -n $stacked_past ]]; then actual+=", past #$stacked_past"; fi
    if grep -q '^paged: stopped #1 \[lower\]: ' "$dir/out"; then actual+=", paged"; fi
  elif (( status == 3 )); then
    actual="armed: $(grep -E '^arm: ' "$dir/out" || true)"
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
