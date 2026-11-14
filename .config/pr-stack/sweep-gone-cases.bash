#!/usr/bin/env bash
# `wt:sweep` prunes a worktree that goes away after the listing, as it prunes
# one that git lists as prunable (#7490), run by `check:pr-stack`. A scratch
# repository holds two worktrees beside its primary one. The case takes the
# listing and then removes one worktree, as the run of another seat removes
# its scratch. Then it judges the listing with `sweep-tree.bash` in a shell of
# its own under `set -e`, as the task judges it.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-sweep-gone.XXXXXX")
trap 'rm -rf "$work"' EXIT
failed=0

fail() {
  echo "wt:sweep gone case FAILED: $1"
  echo "  got: $2"
  failed=1
}

source "$here/../cases/scratch.bash"

git init --quiet --initial-branch=main "$work/repo"
cd "$work/repo"
identity
commit a.txt base base
git worktree add --quiet -b gone "$work/gone"
git worktree add --quiet -b stays "$work/stays"
{
  git worktree list --porcelain
  echo
} > "$work/listing"
gone=$(sed -n 's/^worktree \(.*\/gone\)$/\1/p' "$work/listing")
stays=$(sed -n 's/^worktree \(.*\/stays\)$/\1/p' "$work/listing")
git worktree remove --force "$work/gone"

judged=0
got=$(bash -c '
  set -euo pipefail
  source "$1/sweep.bash"
  source "$1/held.bash"
  source "$1/sweep-tree.bash"
  declare -A integrated=() judged=() first_parent=() on_remote=()
  facts=() kept=() pruned=() asked=()
  here=$(realpath .)
  epoch=$(date +%s)
  trunk_ref=main
  remote_read=false
  held_read
  sweep_judge < "$2"
  printf "pruned: %s\n" "${pruned[@]}"
  printf "%s\n" "${facts[@]}" | jq -r "\"fact: \" + .path"
' sweep-gone "$here" "$work/listing" 2>&1) || judged=$?
(( judged == 0 )) || fail "#7490: the judgement of a listing whose worktree went away passes" "$got"
grep -qxF -- "pruned: pruned $gone (gone): its directory went away after the listing" <<< "$got" \
  || fail "#7490: the worktree that went away after the listing is pruned" "$got"
grep -qxF -- "fact: $stays" <<< "$got" || fail "#7490: the worktree that stands has its fact line" "$got"
! grep -qxF -- "fact: $gone" <<< "$got" || fail "#7490: the worktree that went away has no fact line" "$got"

(( failed == 0 )) || exit 1
echo "wt:sweep gone OK: 4 cases; a worktree removed after the listing is pruned, and the judgement goes on"
