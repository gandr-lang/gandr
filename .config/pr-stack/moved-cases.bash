#!/usr/bin/env bash
# The act after a push that moves the trunk from outside the merge queue
# (#6700, `trunk_moved`), run by `check:pr-stack`. A scratch bare origin holds
# the trunk `landing` and five stacks on its old tip. Then a push from
# outside the queue moves `landing`, and a sixth stack opens on the new tip.
# The open pull requests are read from a stub of `landable_prs`:
# - #1 under #2, a stack of two, is restacked: each member holds the new
#   tip and its own commit, and #2 still holds #1.
# - #5 is queued at the first reading and out of the queue at the next. The
#   act waits for it and then restacks it.
# - #3 stays queued past the wait. It never moves.
# - #4 changes the file that the push changes. Its restack conflicts, so it
#   stays, and the act names it, its lane and the file.
# - #6 stands on the new tip. It stays.
# The act returns 3, for #4 stopped.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
source "$here/stack.bash"
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-moved.XXXXXX")
trap 'drop_scratch; rm -rf "$work"' EXIT
repo=case/case
trunk=landing
failed=0
export XDG_CACHE_HOME=$work/cache REPLAY_ARTIFACTS=$work/artifacts.json
echo '[]' > "$REPLAY_ARTIFACTS"

source "$here/../cases/scratch.bash"

fail() {
  echo "pr-stack moved case FAILED: $1"
  echo "  got: $2"
  failed=1
}

git init --quiet --bare --initial-branch=landing "$work/origin.git"
git clone --quiet "$work/origin.git" "$work/clone" 2> /dev/null
cd "$work/clone"
identity
commit trunk.txt base base
git push --quiet origin landing
git switch --quiet --create engine-1-a landing
commit a.txt a 'a of #1'
git switch --quiet --create engine-2-b
commit b.txt b 'b of #2'
git switch --quiet --create reduction-3-q landing
commit q.txt q 'q of #3'
git switch --quiet --create floor-4-c landing
commit trunk.txt mine 'c of #4'
git switch --quiet --create spaces-5-w landing
commit w.txt w 'w of #5'
git push --quiet origin engine-1-a engine-2-b reduction-3-q floor-4-c spaces-5-w
git switch --quiet landing
commit trunk.txt theirs 'a repair pushed from outside the queue'
git push --quiet origin landing
git switch --quiet --create workflow-6-n landing
commit n.txt n 'n of #6'
git push --quiet origin workflow-6-n
git fetch --quiet origin

before=$(git rev-parse origin/reduction-3-q origin/floor-4-c origin/workflow-6-n)
echo 0 > "$work/readings"
# The open pull requests: #5 queued at the first reading alone.
landable_prs() {
  local n
  n=$(($(< "$work/readings") + 1))
  echo "$n" > "$work/readings"
  jq -nc --argjson first "$([[ $n == 1 ]] && echo true || echo false)" '[
    {number: 5, head: "spaces-5-w", base: "landing", landing: $first},
    {number: 1, head: "engine-1-a", base: "landing", landing: false},
    {number: 2, head: "engine-2-b", base: "engine-1-a", landing: false},
    {number: 3, head: "reduction-3-q", base: "landing", landing: true},
    {number: 4, head: "floor-4-c", base: "landing", landing: false},
    {number: 6, head: "workflow-6-n", base: "landing", landing: false}
  ] | map(. + {created: "2026-11-11T00:00:00Z", bot: false, hold: null})'
}
landed_heads() { :; }
pushed_heads() { :; }
status=0
out=$(TRUNK_MOVED_WAIT=5 TRUNK_MOVED_POLL=1 trunk_moved 2>&1) || status=$?
git fetch --quiet origin

[[ $status == 3 ]] || fail "#6700: a stack whose restack stops makes the act return 3" "exit $status; $out"

# Whether branch `$1` on the origin holds the new tip of `landing`.
on_tip() { git merge-base --is-ancestor origin/landing "origin/$1" && echo "on the tip" || echo "off the tip"; }

got="$(on_tip engine-1-a), $(git log --format=%s origin/landing..origin/engine-2-b | paste -sd ',' -); $(git merge-base --is-ancestor origin/engine-1-a origin/engine-2-b && echo holds || echo lacks) #1"
[[ $got == "on the tip, b of #2,a of #1; holds #1" ]] \
  || fail "#6700: a stack of two moves onto the new tip, each member with its own commit, the upper on the lower" "$got"

got="$(on_tip spaces-5-w), $(git log --format=%s origin/landing..origin/spaces-5-w | paste -sd ',' -)"
[[ $got == "on the tip, w of #5" && $out == *"stack #5: restacked onto"* ]] \
  || fail "#6700: a stack whose member leaves the queue during the wait is restacked" "$got; $out"

after=$(git rev-parse origin/reduction-3-q origin/floor-4-c origin/workflow-6-n)
[[ $after == "$before" ]] || fail "#6700: a queued, a conflicting and a current stack stay where they stand" "$after"

[[ $out == *"stack #3: #3 stays in the merge queue"* ]] \
  || fail "#6700: a stack queued past the wait is named and left to its heal" "$out"
[[ $out == *"stopped #4 [floor]: "*"trunk.txt"* ]] \
  || fail "#6700: a restack that conflicts names its stack, its lane and the file" "$out"
[[ $out == *"stack #6: stands on the tip of landing"* ]] \
  || fail "#6700: a stack on the new tip is named and stays" "$out"

(( failed == 0 )) || exit 1
echo "pr-stack moved OK: after a push from outside the queue, each open stack moves onto the new tip, a queued member is waited for and never moved, and a conflict is named with its lane"
