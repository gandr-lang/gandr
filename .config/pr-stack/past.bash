#!/usr/bin/env bash
# The restack past a red member (#4642), run by `check:pr-stack` over the
# cases in `past.json`. Each case builds a scratch repository with a local
# bare origin: a red branch with one commit of its own, under an upper and a
# top with one each, and, when the case's `red` is `middle`, over a lower with
# one. The upper's commit adds a file of its own when `upper` is `apart`, and
# rewrites the red branch's file when it is `builds`. Pull requests are
# numbered lower 1, red 2, upper 3, top 4, in server stack 9; `gh` and
# `stack_link` are recorded, not run. The result is one line compared with the
# case's `output`: the subjects main..<branch> holds for the upper, the top
# and the red branch, or `refused: conflicts (<files>)` and `, moved` should
# the refused cut have moved a branch, then the `gh` calls and the chain
# linked.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
source "$here/stack.bash"
cases=$here/past.json
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-past.XXXXXX")
trap 'rm -rf "$work"' EXIT
repo=case/case
trunk=main
failed=0

commit() { printf '%s\n' "$2" > "$1" && git add "$1" && git commit --quiet --message "$3"; }
subjects() { git log --format=%s "origin/main..origin/$1" | paste -sd ',' - | sed 's/,/, /g'; }

# The scratch stack in `$1`: the red member `$2` (`middle` or `bottom`) and
# the upper `$3` (`apart` or `builds`).
scenario() {
  git init --quiet --bare --initial-branch=main "$1/origin.git"
  git clone --quiet "$1/origin.git" "$1/clone" 2> /dev/null
  cd "$1/clone"
  git config user.name case
  git config user.email case@example.invalid
  git config commit.gpgsign false
  commit base.txt base base
  git push --quiet origin main
  if [[ $2 == middle ]]; then
    git switch --quiet --create lower
    commit l.txt lower "lower's own"
  fi
  git switch --quiet --create red
  commit r.txt red "red's own"
  git switch --quiet --create upper
  if [[ $3 == apart ]]; then commit u.txt upper "upper's own"; else commit r.txt upper "upper's own"; fi
  git switch --quiet --create top
  commit t.txt top "top's own"
  if [[ $2 == middle ]]; then git push --quiet origin lower; fi
  git push --quiet origin red upper top
}

count=$(jq length "$cases")
for (( i = 0; i < count; i++ )); do
  name=$(jq -r ".[$i].name" "$cases")
  expected=$(jq -r ".[$i].output" "$cases")
  red=$(jq -r ".[$i].red" "$cases")
  dir=$work/$i
  mkdir "$dir"
  scenario "$dir" "$red" "$(jq -r ".[$i].upper" "$cases")"
  cd "$dir/clone"
  : > "$dir/gh"
  : > "$dir/link"
  gh() { printf '%s\n' "$*" >> "$dir/gh"; }
  stack_of() { echo 9; }
  stack_link() { jq -r 'map(.number) | join(" ")' <<< "$1" > "$dir/link"; }
  stack='[{"number":2,"head":"red"},{"number":3,"head":"upper"},{"number":4,"head":"top"}]'
  if [[ $red == middle ]]; then stack=$(jq -c '[{"number":1,"head":"lower"}] + .' <<< "$stack"); fi
  before=$(git rev-parse origin/upper origin/top origin/red)
  if restack_past "$stack" 2 > "$dir/out" 2>&1; then
    actual="moved: upper holds $(subjects upper); top holds $(subjects top); red holds $(subjects red)"
  else
    actual="refused: conflicts ($(grep -o -E 'conflicts \([^)]*\)' "$dir/out" | head -n 1 | sed -E 's/conflicts \((.*)\)/\1/' || true))"
    git fetch --quiet origin
    [[ $(git rev-parse origin/upper origin/top origin/red) == "$before" ]] || actual+=", moved"
  fi
  actual+="; gh: $(paste -sd '|' "$dir/gh" | sed 's/|/ | /g'); link: $(cat "$dir/link")"
  cd - > /dev/null
  if [[ $actual != "$expected" ]]; then
    printf 'pr-stack past case %s\n  expected: %s\n  actual:   %s\n' "$name" "$expected" "$actual" >&2
    sed 's/^/    /' "$dir/out" >&2
    failed=1
  fi
done
(( failed == 0 )) || exit 1
echo "pr-stack past OK: $count cases restack past a red member as recorded"
