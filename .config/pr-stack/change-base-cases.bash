#!/usr/bin/env bash
# The commit `pr:land` reads a stacked pull request's change from (#6055,
# #6062), run by `check:pr-stack`. Each case builds a scratch repository with
# a local bare origin. The trunk holds a base commit. The branch `below` adds
# one commit, and the branch `own` is stacked on it with one commit of its
# own, its worktree recording `below`'s head as its stack base, as `pr:open`
# does. The case then moves `below` or the trunk, and `change_base` names the
# commit `own`'s change is read from. A stub of `gh` answers the open pull
# requests that carry a commit, and counts its calls.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
source "$here/stack.bash"
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-change-base.XXXXXX")
trap 'rm -rf "$work"' EXIT
trunk=main
repo=gandr-lang/gandr
failed=0

source "$here/../cases/scratch.bash"

fail() {
  printf 'pr-stack change-base case %s\n  got: %s\n' "$1" "$2" >&2
  failed=1
}

# The open pull requests that carry a commit: `$open_lower` names the one
# below, or nothing when it merged. Each call is counted in `$work/calls`.
gh() {
  echo call >> "$work/calls"
  if [[ -n ${open_lower:-} ]]; then printf '%s\n' "$open_lower"; fi
}

# The REST calls counted so far, as a bare number. darwin's `wc` writes its
# count right-aligned in a field of eight columns, and GNU `wc` writes none;
# the arithmetic expansion reads both as the number (#6086).
calls() {
  echo $(($(wc -l < "$work/calls")))
}

# A scratch origin at `$1/origin.git` and a clone at `$1/branch` on `own`,
# stacked on `below` with one commit, both pushed. `stacked` names the head of
# `below` that `own` records.
setup() {
  : > "$work/calls"
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

# What `change_base` names for `own` on base `$1`: the files of the change
# read from it, or the refusal with the replay it names, and the REST calls.
judged() {
  local status=0 from
  from=$(change_base "$1" own 2) || status=$?
  if (( status == 0 )); then
    echo "change $(git diff --name-only "$from" origin/own | paste -sd ' ' -), calls $(calls)"
  else
    echo "refused, $([[ $from == *"git rebase --onto origin/$1 ${stacked:0:12}"* ]] && echo "replays from the record" || echo "replays from another commit"), calls $(calls)"
  fi
}

# The pull request below, a base of its own, is amended: the base no longer
# holds the record, so the branch's parent is stale. No REST call is made.
got=$(
  setup "$work/amended"
  git switch --quiet below
  git commit --quiet --amend --message 'below, amended (#1)'
  git push --quiet --force origin below
  git switch --quiet own
  git fetch --quiet origin
  open_lower=1 judged below
)
[[ $got == "refused, replays from the record, calls 0" ]] || fail "#6055: a branch on an amended pull request's old head is refused with the replay" "$got"

# The pull request below moves ahead: its new head still holds the record, so
# the change is read from the merge base, as before.
got=$(
  setup "$work/ahead"
  git switch --quiet below
  commit more.txt more 'below, more (#1)'
  git push --quiet origin below
  git switch --quiet own
  git fetch --quiet origin
  judged below
)
[[ $got == "change own.txt, calls 0" ]] || fail "#6055: a branch whose base moved ahead reads from the merge base" "$got"

# A worktree not on the pull request's head reads from the merge base: the
# record it keeps is another branch's.
got=$(
  setup "$work/elsewhere"
  git switch --quiet below
  git commit --quiet --amend --message 'below, amended (#1)'
  git push --quiet --force origin below
  git fetch --quiet origin
  judged below
)
[[ $got == "change below.txt own.txt, calls 0" ]] || fail "#6055: a worktree not on the pull request's head reads from the merge base" "$got"

# A branch replayed onto the amended head carries the record no more, so it
# reads from the merge base.
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
  judged below
)
[[ $got == "change own.txt, calls 0" ]] || fail "#6055: a branch replayed onto the amended head reads from the merge base" "$got"

# On the trunk, the pull request below stays open while the queue holds it:
# the change is read from the record, so it is the branch's own file alone.
got=$(
  setup "$work/queued"
  open_lower=1 judged main
)
[[ $got == "change own.txt, calls 1" ]] || fail "#6062: a branch on the trunk above an open pull request reads its own change from the record" "$got"

# On the trunk, a record that no open pull request carries is an old copy of
# the one below, merged under new hashes: refused with the replay.
got=$(
  setup "$work/merged"
  git switch --quiet main
  git cherry-pick --quiet -x "$stacked" > /dev/null
  git push --quiet origin main
  git switch --quiet own
  git fetch --quiet origin
  judged main
)
[[ $got == "refused, replays from the record, calls 1" ]] || fail "#6062: a branch on the trunk whose record no open pull request carries is refused with the replay" "$got"

# A `wc` that pads its count, as darwin's does, reads as the bare number all
# the same: two calls read as `2`.
got=$(
  wc() { printf '%8d\n' "$(command wc -l)"; }
  : > "$work/calls"
  gh > /dev/null
  gh > /dev/null
  calls
)
[[ $got == 2 ]] || fail "#6086: a count that wc pads, as on darwin, reads as the bare number" "$got"

(( failed == 0 )) || exit 1
echo "pr-stack change base OK: 7 cases refuse a stale parent with the replay, read from the merge base where the base holds the record, read from the record above an open pull request on the trunk, and read a padded call count as its number"
