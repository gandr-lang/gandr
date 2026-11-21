#!/usr/bin/env bash
# The replay on a runner reads the generated artifacts it can leave stale
# (#6159), run by `check:replay` over the cases in `replays.json`. Each case
# builds a scratch repository with a local bare origin: the branch `b` holds
# one commit of its own, which writes `u.txt`, and stands on `main`, which
# then moves `a.txt`. `signed_restack` rebases `b` onto `main` with the
# `github` signer, and `signed_replay` moves the branch by a plain push of the
# replay. A case's `artifacts` is the table of generated artifacts the replay
# reads (`REPLAY_ARTIFACTS`). The result is one line compared with the case's
# `output`: the status, the first line on stderr and the subjects main..b
# holds on the origin.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
source "$here/../pr-stack/stack.bash"
cases=$here/replays.json
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-replays.XXXXXX")
trap 'rm -rf "$work"' EXIT
repo=case/case
trunk=main
failed=0

source "$here/../cases/scratch.bash"
signed_replay() { git push --quiet --force origin "$3:refs/heads/$1" && echo "$3"; }

count=$(jq length "$cases")
for (( i = 0; i < count; i++ )); do
  name=$(jq -r ".[$i].name" "$cases")
  expected=$(jq -r ".[$i].output" "$cases")
  dir=$work/$i
  mkdir "$dir"
  git init --quiet --bare --initial-branch=main "$dir/origin.git"
  git clone --quiet "$dir/origin.git" "$dir/clone" 2> /dev/null
  cd "$dir/clone"
  identity
  commit a.txt base base
  git switch --quiet --create b
  commit u.txt own "b's own"
  git switch --quiet main
  commit a.txt moved "main moves a.txt"
  git push --quiet origin main b
  jq -c ".[$i].artifacts" "$cases" > "$dir/artifacts.json"
  export REPLAY_ARTIFACTS=$dir/artifacts.json
  status=0
  signed_restack b "$(git rev-parse origin/b)" main > /dev/null 2> "$dir/out" || status=$?
  git fetch --quiet origin
  actual="status $status; $(head -n 1 "$dir/out"); b holds $(git log --format=%s origin/main..origin/b | paste -sd ',' - | sed 's/,/, /g')"
  cd - > /dev/null
  if [[ $actual != "$expected" ]]; then
    printf 'replay case %s\n  expected: %s\n  actual:   %s\n' "$name" "$expected" "$actual" >&2
    sed 's/^/    /' "$dir/out" >&2
    failed=1
  fi
done
(( failed == 0 )) || exit 1
echo "replays OK: $count cases of a runner's replay hold or move the branch as recorded"
