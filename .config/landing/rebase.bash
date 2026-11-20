#!/usr/bin/env bash
# The landing rebase (#5441): `landing` takes each fix that `main` holds and
# `landing` lacks. The integration cycle's job on the factory runner runs it
# after a green verdict, when `ci:cycle` reads such a fix (`fixes.bash`). The
# workflow lane runs it by hand after it resolves a conflict (`mise run
# landing:rebase`). Thus `landing` takes the fix with no merge commit and no
# revert. Nothing rewrites `main`.
#
# - A fix is a commit of `main`, not a merge, whose patch `landing` lacks
#   (`fixes.bash`, #6683). A merge of `landing` into `integration` is no fix,
#   and a commit that `landing` holds under another hash is no fix either.
#   With no fix, `landing` stays.
# - The floor is the newest head of `landing` that `integration` holds: the
#   merge base of the two. The rebase never moves the floor or a commit
#   below it (#6683), so the next take of `landing` merges with no conflict.
#   Git puts each fix on the floor, signed, and skips a fix that becomes
#   empty there. Then git rebases the commits of `landing` above the floor
#   onto the fixes, with their merges. The rebase moves no other branch,
#   whatever `rebase.updateRefs` says. The key of the host signs each new
#   commit.
# - A git note on each moved commit under `refs/notes/rebased` holds its new
#   hash, so a seat finds a landed commit from its old hash.
# - The merge queue builds each group on the tip of `landing`, and a push
#   from outside the queue makes it build each group again (#6553). So
#   before it moves `landing`, the task waits while the remote holds a branch
#   of the queue's groups (`gh-readonly-queue/landing/*`), and reads the tips
#   again after each wait. Git reads the branches, with no API call. The
#   wait ends after `REBASE_QUEUE_WAIT` seconds, 1500 by default, and then
#   the push names each group that it makes the queue build again.
# - One atomic push moves `landing` and the notes. The lease on the old tip
#   of `landing` refuses the push when a landing arrives during the rebase.
#   Then the task reads the tips again, at most 3 times in all.
# - After the push, each open stack lacks the new tip, so the task restacks
#   them onto it (#6700, `.config/pr-stack/moved.bash`). It waits for a
#   queued member up to `TRUNK_MOVED_WAIT` seconds, 300 by default here, and
#   then leaves that stack to its `pr:watch`. A restack that stops pages the
#   stack's seats and leaves the rebase green: `landing` is moved.
#   `REBASE_MOVED` names another command for that act.
# - A fix or a rebase that conflicts stops before the push and exits 3. A
#   fetch or another git command that fails stops the attempt and exits 1.
#   Either way `landing` stays as it was, and the job pages the workflow
#   lane.
#
# Usage: rebase.bash [remote], `origin` by default, in a clone that holds the
# whole history of `main`, `landing` and `integration`.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
remote=${1:-origin}
notes=refs/notes/rebased
scratch=$(mktemp -d)
queue_wait=${REBASE_QUEUE_WAIT:-1500}
queue_poll=${REBASE_QUEUE_POLL:-30}
queue_until=$((SECONDS + queue_wait))
cleanup() {
  git worktree remove --force "$scratch/tree" 2> /dev/null || true
  rm -rf "$scratch"
}
trap cleanup EXIT
# Git gives the hook each pair of an old commit and its new one.
mkdir "$scratch/hooks"
printf '#!/usr/bin/env bash\ncat >> %q\n' "$scratch/rewritten" > "$scratch/hooks/post-rewrite"
chmod +x "$scratch/hooks/post-rewrite"

# One attempt: 0 when `landing` holds each patch of `main` at the end, 3 on
# a conflict, 4 when the push loses its lease, 5 after a wait for the queue's
# groups, and 1 when a fetch or another git command fails or the remote
# refuses the push. The loop below calls `attempt` on the left of `||`, where
# bash ignores `set -e`. Thus each command that can fail returns on its own
# (#5627).
attempt() {
  local main landing integration fixes floor onto new old moved listed=0 refspecs=()
  if ! git fetch --quiet --no-tags "$remote" "+refs/heads/main:refs/remotes/$remote/main" \
    "+refs/heads/landing:refs/remotes/$remote/landing" \
    "+refs/heads/integration:refs/remotes/$remote/integration"; then
    echo "git fetch of main, landing and integration from $remote fails: no rebase runs" >&2
    return 1
  fi
  # `--exit-code` gives 2 when the remote holds no notes. Only 2 means that.
  git ls-remote --exit-code "$remote" "$notes" > /dev/null || listed=$?
  case $listed in
    0)
      if ! git fetch --quiet --no-tags "$remote" "+$notes:$notes"; then
        echo "git fetch of $notes from $remote fails: no rebase runs" >&2
        return 1
      fi
      ;;
    2) ;;
    *)
      echo "git ls-remote of $notes on $remote fails with exit $listed: no rebase runs" >&2
      return 1
      ;;
  esac
  main=$(git rev-parse "refs/remotes/$remote/main") || return 1
  landing=$(git rev-parse "refs/remotes/$remote/landing") || return 1
  integration=$(git rev-parse "refs/remotes/$remote/integration") || return 1
  fixes=$("$here/fixes.bash" "$main" "$landing") || return 1
  if [[ -z $fixes ]]; then
    echo "landing at ${landing:0:12} holds each patch of main at ${main:0:12}: nothing to rebase"
    return 0
  fi
  local groups
  if ! groups=$(git ls-remote "$remote" 'refs/heads/gh-readonly-queue/landing/*'); then
    echo "git ls-remote of the merge queue's groups on $remote fails: no rebase runs" >&2
    return 1
  fi
  if [[ -n $groups ]] && (( SECONDS < queue_until )); then
    echo "the merge queue builds $(wc -l <<< "$groups" | tr -d ' ') group(s) on landing at ${landing:0:12}: the rebase waits for them"
    sleep "$queue_poll"
    return 5
  fi
  if [[ -n $groups ]]; then
    echo "the merge queue still builds these groups after a wait of ${queue_wait}s, and the push makes it build each again: $(awk '{ sub("refs/heads/gh-readonly-queue/landing/", "", $2); print $2 }' <<< "$groups" | paste -sd ' ' -)" >&2
  fi
  # The floor: the newest head of `landing` that `integration` holds. Nothing
  # at or below it moves (#6683).
  floor=$(git merge-base "$landing" "$integration") || return 1
  : > "$scratch/rewritten"
  git worktree add --quiet --detach "$scratch/tree" "$floor" || return 1
  local conflicted
  # shellcheck disable=SC2086 # one fix a word
  if ! git -C "$scratch/tree" cherry-pick --gpg-sign --empty=drop $fixes > /dev/null 2> "$scratch/rebase.err"; then
    conflicted=$(git -C "$scratch/tree" diff --name-only --diff-filter=U | paste -sd ' ' -)
    git -C "$scratch/tree" cherry-pick --abort || true
    if [[ -z $conflicted ]]; then
      echo "the fixes of main at ${main:0:12} do not go on landing's floor at ${floor:0:12}: $(< "$scratch/rebase.err")" >&2
      return 1
    fi
    echo "the fixes of main at ${main:0:12} conflict on landing's floor at ${floor:0:12} in $conflicted" >&2
    return 3
  fi
  onto=$(git -C "$scratch/tree" rev-parse HEAD) || return 1
  if [[ $floor != "$landing" ]] \
    && ! git -C "$scratch/tree" -c core.hooksPath="$scratch/hooks" -c rebase.updateRefs=false \
      rebase --quiet --gpg-sign --rebase-merges --onto "$onto" "$floor" "$landing" > /dev/null 2> "$scratch/rebase.err"; then
    conflicted=$(git -C "$scratch/tree" diff --name-only --diff-filter=U | paste -sd ' ' -)
    git -C "$scratch/tree" rebase --abort || true
    if [[ -z $conflicted ]]; then
      echo "the rebase of landing at ${landing:0:12} above its floor at ${floor:0:12} fails: $(< "$scratch/rebase.err")" >&2
      return 1
    fi
    echo "the rebase of landing at ${landing:0:12} above its floor at ${floor:0:12} conflicts in $conflicted" >&2
    return 3
  fi
  new=$(git -C "$scratch/tree" rev-parse HEAD) || return 1
  git worktree remove --force "$scratch/tree" || return 1
  if [[ $new == "$landing" ]]; then
    echo "each fix of main at ${main:0:12} is empty on landing at ${landing:0:12}: nothing moves"
    return 0
  fi
  # A side branch that leaves `landing` below the floor keeps its commits,
  # and the hook names each of them as its own new commit. Only a moved
  # commit gets a note.
  local count=0
  while read -r old moved _; do
    [[ $old == "$moved" ]] && continue
    git notes --ref=rebased add --force --message "$moved" "$old" || return 1
    count=$((count + 1))
  done < "$scratch/rewritten"
  refspecs+=("$notes:$notes")
  echo "$(wc -w <<< "$fixes" | tr -d ' ') fix(es) of main at ${main:0:12} go on landing's floor at ${floor:0:12}, the head that integration holds, and $count of landing's commits above it move: landing goes to ${new:0:12}"
  if ! git push --quiet --atomic --force-with-lease="refs/heads/landing:$landing" "$remote" \
    "$new:refs/heads/landing" "${refspecs[@]}"; then
    # The lease fails only when `landing` moved. Any other refusal leaves it.
    [[ $(git ls-remote "$remote" refs/heads/landing) == "$landing"* ]] && return 1
    return 4
  fi
  pushed=true
  return 0
}

pushed=false
try=1
while (( try <= 3 )); do
  status=0
  attempt || status=$?
  case $status in
    0)
      if [[ $pushed == true ]]; then
        TRUNK_MOVED_WAIT=${TRUNK_MOVED_WAIT:-300} "${REBASE_MOVED:-$here/../pr-stack/moved.bash}" \
          || echo "the restack of the open stacks onto the new landing stops; its seats are paged" >&2
      fi
      exit 0
      ;;
    4)
      echo "the push of landing lost its lease on try $try: a landing arrived during the rebase" >&2
      try=$((try + 1))
      ;;
    5) ;;
    *) exit "$status" ;;
  esac
done
echo "the push of landing lost its lease 3 times" >&2
exit 4
