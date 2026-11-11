#!/usr/bin/env bash
# A stack on an old lineage of the trunk (#6399, `replay_lineage`), which
# `land_prefix` replays before it queues anything, run by `check:pr-stack`
# over the cases in `lineage.json`. Each case builds a scratch repository
# with a local bare origin. The trunk holds a base and four landed commits.
# The branch `lower` (pull request 2) is cut from the trunk's tip with one
# commit of its own, and `upper` (pull request 3) stacks on it with one
# commit. A case's `setup` then moves the trunk:
# - `rewritten`: as the landing rebase rewrites `landing`, the landed commits
#   move onto a repair under other hashes, and a later commit changes a file
#   that the first of them adds; with `note` true, a note under
#   `refs/notes/rebased` names the new tip;
# - `behind`: the trunk gains one commit, and the stack is only behind it.
# `gh`, `queue_stack` and the readings of the server are recorded, not run,
# and every member reads green. `signed_replay` moves a branch by a plain push
# of the replay, and writes `replay <branch>` among the `gh` calls. The result
# is one line compared with the case's `output`: the status of
# `land_prefix`, its last line on stderr, the subjects that main..<branch>
# holds for each member, and the `gh` calls.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
source "$here/stack.bash"
cases=$here/lineage.json
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-lineage.XXXXXX")
trap 'rm -rf "$work"' EXIT
export GANDR_HOST_LOCK_DIR=$work
repo=case/case
trunk=main
failed=0

source "$here/../cases/scratch.bash"
subjects() { git log --format=%s "origin/main..origin/$1" | paste -sd ',' - | sed 's/,/, /g'; }

# The scratch stack in `$1`, the trunk moved as `$2` says, noted when `$3`
# is true.
scenario() {
  local old_tip landed
  git init --quiet --bare --initial-branch=main "$1/origin.git"
  git clone --quiet "$1/origin.git" "$1/clone" 2> /dev/null
  cd "$1/clone"
  identity
  commit base.txt base base
  for landed in 1 2 3 4; do commit "landed-$landed.txt" "landed $landed" "landed (#1$landed)"; done
  git push --quiet origin main
  old_tip=$(git rev-parse HEAD)
  git switch --quiet --create lower
  commit lower.txt lower "lower's own"
  git switch --quiet --create upper
  commit upper.txt upper "upper's own"
  git push --quiet origin lower upper
  git switch --quiet main
  if [[ $2 == behind ]]; then
    commit later.txt later 'later (#15)'
    git push --quiet origin main
    return
  fi
  git reset --quiet --hard HEAD~4
  commit repair.txt repair 'repair (#16)'
  git cherry-pick --quiet "$old_tip~4..$old_tip" > /dev/null
  commit landed-1.txt 'landed 1, repaired' 'landed (#11) repaired'
  [[ $3 != true ]] || git notes --ref=rebased add --message "$(git rev-parse HEAD)" "$old_tip"
  git push --quiet --force origin main
  [[ $3 != true ]] || git push --quiet origin refs/notes/rebased
}

stack='[{"number":2,"head":"lower"},{"number":3,"head":"upper"}]'
count=$(jq length "$cases")
for (( i = 0; i < count; i++ )); do
  name=$(jq -r ".[$i].name" "$cases")
  expected=$(jq -r ".[$i].output" "$cases")
  case_dir=$work/$i
  mkdir "$case_dir"
  scenario "$case_dir" "$(jq -r ".[$i].setup" "$cases")" "$(jq -r ".[$i].note" "$cases")"
  cd "$case_dir/clone"
  : > "$case_dir/gh"
  gh() { printf '%s\n' "$*" >> "$case_dir/gh"; }
  open_prs() { echo '[]'; }
  server_stack() { echo "$stack"; }
  queued_of() { echo '[]'; }
  carried_queued() { echo '[]'; }
  required_contexts() { echo '[]'; }
  queue_unit_cap() { echo 0; }
  required_state() { echo green; }
  hold_landing() { :; }
  release_landing() { :; }
  queue_stack() { printf 'queue up to %s\n' "$3" >> "$case_dir/gh"; }
  signed_replay() { printf 'replay %s\n' "$1" >> "$case_dir/gh"; git push --quiet --force origin "$3:refs/heads/$1" && echo "$3"; }
  unset REPLAY_ARTIFACTS
  status=0
  land_prefix 3 2> "$case_dir/out" || status=$?
  git fetch --quiet origin
  actual="status $status; $(awk 'NF { line = $0 } END { print line }' "$case_dir/out"); lower holds $(subjects lower); upper holds $(subjects upper)"
  actual+="; gh: $(paste -sd '|' "$case_dir/gh" | sed 's/|/ | /g')"
  cd - > /dev/null
  if [[ $actual != "$expected" ]]; then
    printf 'pr-stack lineage case %s\n  expected: %s\n  actual:   %s\n' "$name" "$expected" "$actual" >&2
    sed 's/^/    /' "$case_dir/out" >&2
    failed=1
  fi
done
(( failed == 0 )) || exit 1
echo "pr-stack lineage OK: $count cases replay a stack off an old lineage of the trunk before it queues"
