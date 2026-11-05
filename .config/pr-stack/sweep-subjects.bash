#!/usr/bin/env bash
# `wt:sweep` judges a branch landed by subject only against the commits the
# trunk gains after the branch forks (#5118), run by `check:pr-stack` over
# the cases in `subjects.json`. A scratch repository holds two branches, each
# read by `own_commits` and decided by `sweep.jq` as the sweep decides it:
# - `repeat` forks after the trunk's commit `S` and commits another patch
#   under the subject `S`;
# - `landed` commits `T`, and the trunk then gains `T (#2)` with another
#   patch, as a queue merge after a conflicted rebase gives it (#4227).
# A case names its branch and the decision, `<action>: <reason>`.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
source "$here/sweep.bash"
cases=$here/subjects.json
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-sweep-subjects.XXXXXX")
trap 'rm -rf "$work"' EXIT
failed=0

source "$here/../cases/scratch.bash"

cd "$work"
git init --quiet --initial-branch=main .
identity
commit a.txt base base
commit a.txt one S
git switch --quiet --create repeat
commit a.txt two S
git switch --quiet main
git switch --quiet --create landed
commit b.txt x T
git switch --quiet main
commit b.txt y 'T (#2)'

count=$(jq length "$cases")
for (( i = 0; i < count; i++ )); do
  name=$(jq -r ".[$i].name" "$cases")
  branch=$(jq -r ".[$i].branch" "$cases")
  expected=$(jq -r ".[$i].output" "$cases")
  commits=$(own_commits main "$branch")
  ahead=$(git rev-list --count "main..$branch")
  actual=$(jq -nc --arg branch "$branch" --argjson commits "$commits" --argjson ahead "$ahead" \
    '{path: "/w/\($branch)", branch: $branch, primary: false, cwd: false, merged: false, moved: false,
      scratch: null, watched: null, commits: $commits, ahead: $ahead, pulls: null, idle: false}' \
    | jq -s -r -f "$here/sweep.jq" | jq -r '.[0] | "\(.action): \(.reason)"')
  if [[ $actual != "$expected" ]]; then
    printf 'wt:sweep subject case %s\n  expected: %s\n  actual:   %s\n  commits:  %s\n' "$name" "$expected" "$actual" "$commits" >&2
    failed=1
  fi
done
(( failed == 0 )) || exit 1
echo "wt:sweep subjects OK: $count cases decide as recorded"
