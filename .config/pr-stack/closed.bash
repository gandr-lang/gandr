#!/usr/bin/env bash
# The cut of a chain past a member closed unmerged (#5695, `cut_closed`),
# which `land_prefix` runs through `retarget_bottom`, run by `check:pr-stack`
# over the cases in `closed.json`. Each case builds a scratch repository with
# a local bare origin. The branch `closed` has one commit of its own, and the
# branches `bottom` and `upper` stack on it with one commit each. The pull
# requests are closed 1, bottom 2 and upper 3. The chain is in server stack 9,
# and the origin holds the head of pull request 1 as `refs/pull/1/head`. A
# case's `closed` is true when `closed_pr` reads pull request 1, closed
# unmerged, for the branch `closed`. A case's `setup` is a change made first:
# `moved` adds a commit to `closed` after the chain stacked,
# `gone` deletes the branch `closed`, and `conflict` gives the bottom's commit
# the closed one's file. `gh`, `stack_link` and `queued_of` are recorded, not
# run, and `signed_replay` moves a branch by a plain push of the replay. It
# writes `replay <branch>` among the `gh` calls, so a case reads the base
# change before the first push (#6176). The
# result is one line compared with the case's `output`: the status, the
# first line on stderr, the subjects main..<branch> holds for the bottom and
# the upper, the `gh` calls and each chain linked. A case's `artifacts`, when
# given, is the table of generated artifacts the replay reads before a branch
# moves (#6159, `REPLAY_ARTIFACTS`); on this runner's replay a due row holds
# the branch.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
source "$here/stack.bash"
cases=$here/closed.json
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-closed.XXXXXX")
trap 'rm -rf "$work"' EXIT
export GANDR_HOST_LOCK_DIR=$work
repo=case/case
trunk=main
failed=0

source "$here/../cases/scratch.bash"
subjects() { git log --format=%s "origin/main..origin/$1" | paste -sd ',' - | sed 's/,/, /g'; }

# The scratch chain in `$1`, with the change `$2` (`none`, `moved`, `gone` or
# `conflict`).
scenario() {
  git init --quiet --bare --initial-branch=main "$1/origin.git"
  git clone --quiet "$1/origin.git" "$1/clone" 2> /dev/null
  cd "$1/clone"
  identity
  commit base.txt base base
  git push --quiet origin main
  git switch --quiet --create closed
  commit c.txt closed "closed's own"
  git switch --quiet --create bottom
  if [[ $2 == conflict ]]; then commit c.txt bottom "bottom's own"; else commit b.txt bottom "bottom's own"; fi
  git switch --quiet --create upper
  commit u.txt upper "upper's own"
  git push --quiet origin closed bottom upper closed:refs/pull/1/head
  case $2 in
    moved)
      git switch --quiet closed
      commit c.txt later "closed's later"
      git push --quiet --force origin closed closed:refs/pull/1/head
      ;;
    gone) git push --quiet origin --delete closed ;;
  esac
}

chain='[{"number":2,"head":"bottom"},{"number":3,"head":"upper"}]'
bottom='{"number":2,"base":"closed","landing":false,"stack":9}'
count=$(jq length "$cases")
for (( i = 0; i < count; i++ )); do
  name=$(jq -r ".[$i].name" "$cases")
  expected=$(jq -r ".[$i].output" "$cases")
  read_closed=$(jq -r ".[$i].closed" "$cases")
  # `cut_closed`'s own `dir` shadows a variable of that name.
  case_dir=$work/$i
  mkdir "$case_dir"
  scenario "$case_dir" "$(jq -r ".[$i].setup" "$cases")"
  cd "$case_dir/clone"
  : > "$case_dir/gh"
  : > "$case_dir/link"
  gh() { printf '%s\n' "$*" >> "$case_dir/gh"; }
  stack_of() { if grep -q '^stack unstack' "$case_dir/gh"; then echo null; else echo 9; fi; }
  queued_of() { echo '[]'; }
  stack_link() { jq -r 'map(.number) | join(" ")' <<< "$1" >> "$case_dir/link"; }
  # The open pull requests are the chain's members: the closed one is not
  # open, so `set_base` counts none of its commits (#6797).
  open_prs() { printf '%s\n' "$chain"; }
  signed_replay() { printf 'replay %s\n' "$1" >> "$case_dir/gh"; git push --quiet --force origin "$3:refs/heads/$1" && echo "$3"; }
  closed_pr() {
    if [[ $1 == closed && $read_closed == true ]]; then
      jq -cn --arg oid "$(git ls-remote origin refs/pull/1/head | awk '{ print $1 }')" '{number: 1, head: "closed", base: "main", oid: $oid}'
    else
      echo null
    fi
  }
  unset REPLAY_ARTIFACTS
  if [[ $(jq -r ".[$i].artifacts // empty" "$cases") ]]; then
    jq -c ".[$i].artifacts" "$cases" > "$case_dir/artifacts.json"
    export REPLAY_ARTIFACTS=$case_dir/artifacts.json
  fi
  status=0
  retarget_bottom "$bottom" "$chain" 2> "$case_dir/out" || status=$?
  git fetch --quiet origin
  actual="status $status; $(head -n 1 "$case_dir/out"); bottom holds $(subjects bottom); upper holds $(subjects upper)"
  actual+="; gh: $(paste -sd '|' "$case_dir/gh" | sed 's/|/ | /g'); link: $(paste -sd '|' "$case_dir/link" | sed 's/|/ | /g')"
  cd - > /dev/null
  if [[ $actual != "$expected" ]]; then
    printf 'pr-stack closed case %s\n  expected: %s\n  actual:   %s\n' "$name" "$expected" "$actual" >&2
    sed 's/^/    /' "$case_dir/out" >&2
    failed=1
  fi
done
(( failed == 0 )) || exit 1
echo "pr-stack closed OK: $count cases cut a chain past a member closed unmerged as recorded"
