#!/usr/bin/env bash
# A pull request stacked on the head of another one (#6055), run by
# `check:pr-stack`. Each case builds a scratch repository with a local bare
# origin. The trunk holds a base commit. The branch `below` adds one commit,
# and the branch `own` is stacked on it with one commit of its own, its
# worktree recording `below`'s head as its stack base, as `pr:open` does. The
# case then moves `below`, and `stale_parent` judges `own` against it.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
source "$here/stack.bash"
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-stale-parent.XXXXXX")
trap 'rm -rf "$work"' EXIT
trunk=main
failed=0

source "$here/../cases/scratch.bash"

fail() {
  printf 'pr-stack stale-parent case %s\n  got: %s\n' "$1" "$2" >&2
  failed=1
}

# A scratch origin at `$1/origin.git` and a clone at `$1/branch` on `own`,
# stacked on `below` with one commit, both pushed. `stacked` names the head of
# `below` that `own` records.
setup() {
  git init --quiet --bare --initial-branch=main "$1/origin.git"
  git clone --quiet "$1/origin.git" "$1/branch" 2> /dev/null
  cd "$1/branch"
  identity
  commit a.txt base base
  git push --quiet origin main
  git switch --quiet --create below
  commit below.txt below 'below (#1)'
  git push --quiet origin below
  stacked=$(git rev-parse HEAD)
  git switch --quiet --create own
  record_stack_base HEAD
  commit own.txt own 'own (#2)'
  git push --quiet origin own
  git fetch --quiet origin
}

# The judgement of `own` against `below`: `opens`, or `refused` with what the
# refusal names.
judged() {
  local status=0 refusal
  refusal=$(stale_parent below own) || status=$?
  if (( status == 0 )); then
    echo opens
  else
    echo "refused, $([[ $refusal == *"git rebase --onto origin/below ${stacked:0:12}"* ]] && echo "replays from the record" || echo "replays from another commit")"
  fi
}

# The pull request below is amended: its head moves to a commit that does not
# hold the recorded one, so the branch's parent is stale.
got=$(
  setup "$work/amended"
  git switch --quiet below
  git commit --quiet --amend --message 'below, amended (#1)'
  git push --quiet --force origin below
  git switch --quiet own
  git fetch --quiet origin
  judged
)
[[ $got == "refused, replays from the record" ]] || fail "#6055: a branch on an amended pull request's old head is refused with the replay" "$got"

# The pull request below moves ahead: its new head still holds the recorded
# one, so the branch reads as before.
got=$(
  setup "$work/ahead"
  git switch --quiet below
  commit more.txt more 'below, more (#1)'
  git push --quiet origin below
  git switch --quiet own
  git fetch --quiet origin
  judged
)
[[ $got == "opens" ]] || fail "#6055: a branch whose base moved ahead and holds its record opens" "$got"

# A worktree not on the pull request's head is not judged: the record it keeps
# is another branch's.
got=$(
  setup "$work/elsewhere"
  git switch --quiet below
  git commit --quiet --amend --message 'below, amended (#1)'
  git push --quiet --force origin below
  git fetch --quiet origin
  judged
)
[[ $got == "opens" ]] || fail "#6055: a worktree not on the pull request's head is not judged" "$got"

# A branch replayed onto the amended head carries the record no more, so it
# opens.
got=$(
  setup "$work/replayed"
  git switch --quiet below
  git commit --quiet --amend --message 'below, amended (#1)'
  git push --quiet --force origin below
  git switch --quiet own
  git fetch --quiet origin
  git -c rebase.updateRefs=false rebase --quiet --onto origin/below "$stacked"
  git push --quiet --force origin own
  git fetch --quiet origin
  judged
)
[[ $got == "opens" ]] || fail "#6055: a branch replayed onto the amended head opens" "$got"

(( failed == 0 )) || exit 1
echo "pr-stack stale parent OK: 4 cases refuse a branch on an amended pull request's old head with the replay, and open one whose base moved ahead, one judged elsewhere and one replayed"
