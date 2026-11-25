#!/usr/bin/env bash
# A branch cut from a trunk that the landing rebase rewrites since (#5990),
# run by `check:pr-stack`. Each case builds a scratch repository with a local
# bare origin. The trunk holds one landed commit, and a branch cut from it
# adds one commit of its own. The trunk is then rewritten as the landing
# rebase rewrites `landing`: its landed commit moves onto a fix under another
# hash, and a note under `refs/notes/rebased` names the new hash. A branch
# whose worktree recorded its start (`record_start`, as `wt:warm` does)
# measures from that commit, so its own file alone is its change. A branch
# with no record is refused by `rewritten_base`, which names the old tip to
# replay from. A branch with no record on a trunk that no rebase rewrote is
# not refused, and a record taken after the branch's own commit writes
# nothing.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
source "$here/stack.bash"
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-rewritten-base.XXXXXX")
trap 'rm -rf "$work"' EXIT
trunk=main
failed=0

source "$here/../cases/scratch.bash"
evidence_base() { git merge-base origin/main HEAD; }

fail() {
  printf 'pr-stack rewritten-base case %s\n  got: %s\n' "$1" "$2" >&2
  failed=1
}

# A scratch origin whose trunk holds a base and one landed commit, and a
# clone at `$1/branch` on the branch `own`, cut from the trunk's tip with one
# commit of its own. With `$2` set to `record`, the branch records its start
# before its commit. With `$3` set to `rewrite`, the trunk then moves its
# landed commit onto a fix, and notes the old commit with its new hash.
setup() {
  git init --quiet --bare --initial-branch=main "$1/origin.git"
  git clone --quiet "$1/origin.git" "$1/branch" 2> /dev/null
  cd "$1/branch"
  identity
  commit a.txt base base
  commit landed.txt landed 'landed (#1)'
  git push --quiet origin main
  old_tip=$(git rev-parse HEAD)
  git switch --quiet --create own
  [[ ${2:-} != record ]] || record_start
  commit own.txt own 'own (#2)'
  if [[ ${3:-} == rewrite ]]; then
    git switch --quiet --create rewritten "$old_tip~1"
    commit fix.txt fix 'fix on main'
    git cherry-pick --quiet -x "$old_tip" > /dev/null
    git notes --ref=rebased add --message "$(git rev-parse HEAD)" "$old_tip"
    git push --quiet --force origin rewritten:main refs/notes/rebased
    git switch --quiet own
    git branch --quiet --delete --force rewritten
  fi
  git fetch --quiet origin main
}

# With the record, the branch measures from its start and opens: its change
# is its own file alone.
got=$(
  setup "$work/record" record rewrite
  from=$(measured_from)
  echo "$([[ $from == "$old_tip" ]] && echo "from the record" || echo "from another commit")," \
    "change $(git diff --name-only "$from" HEAD | paste -sd ' ' -)," \
    "$(rewritten_base > /dev/null && echo opens || echo refused)"
)
[[ $got == "from the record, change own.txt, opens" ]] || fail "#5990: a recorded branch on a rewritten trunk measures from its start" "$got"

# Without the record, the merge base reads the old landed commit as the
# branch's own, so the opening is refused with the replay from the old tip.
got=$(
  setup "$work/bare" '' rewrite
  from=$(measured_from)
  status=0
  refusal=$(rewritten_base) || status=$?
  echo "change $(git diff --name-only "$from" HEAD | paste -sd ' ' -)," \
    "exit $status," \
    "$([[ $refusal == *"carries 1 commit(s) that origin/main holds by patch"* ]] && echo "counts 1" || echo "counts another")," \
    "$([[ $refusal == *"git rebase --onto origin/main ${old_tip:0:12}"* ]] && echo "replays from the old tip" || echo "replays from another commit")"
)
[[ $got == "change landed.txt own.txt, exit 1, counts 1, replays from the old tip" ]] || fail "#5990: a branch with no record on a rewritten trunk is refused with the replay" "$got"

# Without the record, on a trunk no rebase rewrote, the branch opens.
got=$(
  setup "$work/plain"
  from=$(measured_from)
  echo "change $(git diff --name-only "$from" HEAD | paste -sd ' ' -)," \
    "$(rewritten_base > /dev/null && echo opens || echo refused)"
)
[[ $got == "change own.txt, opens" ]] || fail "#5990: a branch with no record on a trunk no rebase rewrote opens" "$got"

# A record taken after the branch's own commit writes nothing, so a rerun of
# `wt:warm` never moves the base onto the branch's own commits.
got=$(
  setup "$work/late"
  record_start
  echo "record $([[ -s $(git rev-parse --git-path gandr-stack-base) ]] && echo written || echo none)"
)
[[ $got == "record none" ]] || fail "#5990: a record taken after the branch's own commit writes nothing" "$got"

(( failed == 0 )) || exit 1
echo "pr-stack rewritten base OK: 4 cases measure from the record, refuse a recordless branch on a rewritten trunk, open on a plain one, and keep a late record unwritten"
