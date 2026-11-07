#!/usr/bin/env bash
# The rebase of `landing` onto `main` (#5441). The integration cycle's job on
# the factory runner runs it after a green verdict that carries a fix: `main`
# then holds a commit that `landing` lacks. The workflow lane runs it by hand
# after it resolves a conflict (`mise run landing:rebase`). Thus `landing`
# takes the fix with no merge commit and no revert, and `main` stays a
# fast-forward of `integration`. Nothing rewrites `main`.
#
# - A `landing` that holds `main` needs nothing.
# - A `landing` with no commit past `main` fast-forwards to `main`.
# - Otherwise git rebases `landing`'s commits past `main` onto `main` in a
#   scratch worktree, with their merges. `main` is the rebase's upstream, so
#   git drops each commit whose patch `main` holds under another hash
#   (#5932): a commit that landed on `main` before a rewrite of `landing`.
#   The rebase moves no other branch, whatever `rebase.updateRefs` says. The
#   key of the host signs each new commit.
# - A git note on each old commit under `refs/notes/rebased` holds its new
#   hash, so a seat finds a landed commit from its old hash.
# - One atomic push moves `landing` and the notes. The lease on the old tip
#   of `landing` refuses the push when a landing arrives during the rebase.
#   Then the task reads both tips again, at most 3 times in all.
# - A rebase that conflicts stops before the push and exits 3. A fetch or
#   another git command that fails stops the attempt and exits 1. Either way
#   `landing` stays as it was, and the job pages the workflow lane.
#
# Usage: rebase.bash [remote], `origin` by default, in a clone that holds the
# whole history of `main` and `landing`.
set -euo pipefail
remote=${1:-origin}
notes=refs/notes/rebased
scratch=$(mktemp -d)
cleanup() {
  git worktree remove --force "$scratch/tree" 2> /dev/null || true
  rm -rf "$scratch"
}
trap cleanup EXIT
# Git gives the hook each pair of an old commit and its new one.
mkdir "$scratch/hooks"
printf '#!/usr/bin/env bash\ncat >> %q\n' "$scratch/rewritten" > "$scratch/hooks/post-rewrite"
chmod +x "$scratch/hooks/post-rewrite"

# One attempt: 0 when `landing` holds `main` at the end, 3 on a conflict, 4
# when the push loses its lease, and 1 when a fetch or another git command
# fails or the remote refuses the push. The loop below calls `attempt` on the
# left of `||`, where bash ignores `set -e`. Thus each command that can fail
# returns on its own (#5627).
attempt() {
  local main landing base new old moved listed=0 refspecs=()
  if ! git fetch --quiet --no-tags "$remote" "+refs/heads/main:refs/remotes/$remote/main" \
    "+refs/heads/landing:refs/remotes/$remote/landing"; then
    echo "git fetch of main and landing from $remote fails: no rebase runs" >&2
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
  if git merge-base --is-ancestor "$main" "$landing"; then
    echo "landing at ${landing:0:12} holds main at ${main:0:12}: nothing to rebase"
    return 0
  fi
  base=$(git merge-base "$main" "$landing") || return 1
  if [[ $base == "$landing" ]]; then
    new=$main
    echo "landing at ${landing:0:12} holds no commit past main: it fast-forwards to ${main:0:12}"
  else
    : > "$scratch/rewritten"
    git worktree add --quiet --detach "$scratch/tree" "$landing" || return 1
    if ! git -C "$scratch/tree" -c core.hooksPath="$scratch/hooks" -c rebase.updateRefs=false \
      rebase --quiet --gpg-sign --rebase-merges "$main" > /dev/null 2> "$scratch/rebase.err"; then
      local conflicted
      conflicted=$(git -C "$scratch/tree" diff --name-only --diff-filter=U | paste -sd ' ' -)
      git -C "$scratch/tree" rebase --abort || true
      if [[ -z $conflicted ]]; then
        echo "the rebase of landing at ${landing:0:12} onto main at ${main:0:12} fails: $(< "$scratch/rebase.err")" >&2
        return 1
      fi
      echo "the rebase of landing at ${landing:0:12} onto main at ${main:0:12} conflicts in $conflicted" >&2
      return 3
    fi
    new=$(git -C "$scratch/tree" rev-parse HEAD) || return 1
    git worktree remove --force "$scratch/tree" || return 1
    # A side branch that leaves `main` before the base keeps its commits, and
    # the hook names each of them as its own new commit. Only a moved commit
    # gets a note.
    local count=0
    while read -r old moved _; do
      [[ $old == "$moved" ]] && continue
      git notes --ref=rebased add --force --message "$moved" "$old" || return 1
      count=$((count + 1))
    done < "$scratch/rewritten"
    refspecs+=("$notes:$notes")
    echo "$count of landing's commits past main move onto main at ${main:0:12}: landing goes to ${new:0:12}"
  fi
  if ! git push --quiet --atomic --force-with-lease="refs/heads/landing:$landing" "$remote" \
    "$new:refs/heads/landing" "${refspecs[@]}"; then
    # The lease fails only when `landing` moved. Any other refusal leaves it.
    [[ $(git ls-remote "$remote" refs/heads/landing) == "$landing"* ]] && return 1
    return 4
  fi
  return 0
}

for try in 1 2 3; do
  status=0
  attempt || status=$?
  case $status in
    0) exit 0 ;;
    4) echo "the push of landing lost its lease on try $try: a landing arrived during the rebase" >&2 ;;
    *) exit "$status" ;;
  esac
done
echo "the push of landing lost its lease 3 times" >&2
exit 4
