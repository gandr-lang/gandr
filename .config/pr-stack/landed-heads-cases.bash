#!/usr/bin/env bash
# The remote branches the landing watcher deletes (#6185), run by
# `check:pr-stack` over the cases in `landed-heads.json`. A scratch bare remote
# holds the trunk `landing` and a branch for each case. `branch_reading`
# decides each one, as the watcher reads them, with `stack-top` and
# `stack-base` used by an open pull request. Then `moved` gains a commit on
# the remote, and `branch_delete` deletes the decided heads in one push. A
# case names its branch, the decision `<action>: <reason>`, and whether the
# branch stays after the push.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
pr_stack_dir=$here
source "$here/sweep.bash"
source "$here/landed-heads.bash"
source "$here/../cases/scratch.bash"
cases=$here/landed-heads.json
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-landed-heads.XXXXXX")
trap 'rm -rf "$work"' EXIT
failed=0

git init --quiet --bare --initial-branch=landing "$work/remote.git"
git init --quiet --initial-branch=landing "$work/seat"
cd "$work/seat"
identity
git remote add origin "$work/remote.git"
commit a.txt base base
commit a.txt one S
git branch behind
for branch in landed stack-base stack-top moved; do
  git switch --quiet --create "$branch" landing
  commit "$branch.txt" x "land $branch"
done
git switch --quiet --create open landing
commit open.txt x 'an unlanded step'
git switch --quiet landing
# The trunk gains each landed branch's subject with another patch, as a queue
# merge after a conflicted rebase gives it (#4227).
for branch in landed stack-base stack-top moved; do commit "$branch.txt" y "land $branch (#2)"; done
git push --quiet origin landing behind landed stack-base stack-top moved open \
  "landing:refs/heads/gh-readonly-queue/landing/pr-1-0000000"
git fetch --quiet origin

printf '%s\n' stack-top stack-base > "$work/used"
decisions=$(branch_reading origin origin/landing "$work/used" main landing integration badges)

# `moved` gains a commit on the remote between the read and the push.
git clone --quiet "$work/remote.git" "$work/other"
(cd "$work/other" && identity && git switch --quiet moved && commit late.txt x 'a late step' && git push --quiet origin moved)

pushed=$(branch_delete origin "$decisions" || true)
remaining=$(git ls-remote --heads origin | awk '{ sub("^refs/heads/", "", $2); print $2 }')

count=$(jq length "$cases")
for ((i = 0; i < count; i++)); do
  name=$(jq -r ".[$i].name" "$cases")
  branch=$(jq -r ".[$i].branch" "$cases")
  expected=$(jq -r ".[$i].output" "$cases")
  after=$(jq -r ".[$i].after" "$cases")
  actual=$(jq -r --arg branch "$branch" '.[] | select(.name == $branch) | "\(.action): \(.reason)"' <<< "$decisions")
  if grep -qxF "$branch" <<< "$remaining"; then stays=stays; else stays=gone; fi
  if [[ $actual != "$expected" || $stays != "$after" ]]; then
    printf 'branches case %s\n  expected: %s, %s\n  actual:   %s, %s\n  push:\n%s\n' "$name" "$expected" "$after" "$actual" "$stays" "$pushed" >&2
    failed=1
  fi
done
((failed == 0)) || exit 1
echo "pr-stack landed heads OK: $count cases delete each landed head no pull request uses, in one push that keeps a head moved since the read"
