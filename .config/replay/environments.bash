#!/usr/bin/env bash
# The environment of a replay's check (#7485), run by `check:replay`. Each
# case of `environments.json` builds a scratch repository of three commits:
# the old base, a new base that changes `a.txt`, and a head that adds `u.txt`.
# The head pins the case's `pin` in `rust-toolchain.toml` when the case gives
# one, and holds the case's `env` line under `[env]` in `mise.toml` when the
# case gives one. One row reads `a.txt` into `u.txt` with the case's `check`,
# so the replay makes it due. The caller carries `nightly-seat` and
# `GANDR_REPLAY_CASE=caller`. `stale.bash` runs on the head, and the case
# compares its exit status, a line on stderr that holds `says`, and, for a
# refusal, that the check did not run.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
source "$here/../cases/scratch.bash"
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-replay-environments.XXXXXX")
trap 'rm -rf "$work"' EXIT
export RUSTUP_TOOLCHAIN=nightly-seat GANDR_REPLAY_CASE=caller
failed=0
count=$(jq length "$here/environments.json")
for (( i = 0; i < count; i++ )); do
  case=$(jq -c ".[$i]" "$here/environments.json")
  name=$(jq -r .name <<< "$case")
  dir=$work/$i
  git init --quiet "$dir/repo"
  cd "$dir/repo"
  identity
  commit a.txt one 'old base'
  old=$(git rev-parse HEAD)
  commit a.txt two 'new base'
  new=$(git rev-parse HEAD)
  pin=$(jq -r '.pin // empty' <<< "$case")
  [[ -z $pin ]] || printf '[toolchain]\nchannel = "%s"\n' "$pin" > rust-toolchain.toml
  env=$(jq -r '.env // empty' <<< "$case")
  [[ -z $env ]] || printf '[env]\n%s\n' "$env" > mise.toml
  printf 'own\n' > u.txt
  git add -A
  git commit --quiet --message head
  head=$(git rev-parse HEAD)
  jq -c '[{name: "the head'"'"'s file", paths: ["u.txt"], inputs: ["a.txt"], check: .check, stale: [100], record: "write u.txt again"}]' \
    <<< "$case" > "$dir/artifacts.json"
  status=0
  GANDR_REPLAY_RAN=$dir/ran REPLAY_ARTIFACTS=$dir/artifacts.json "$here/stale.bash" "$old" "$new" "$head" 2> "$dir/err" || status=$?
  cd - > /dev/null
  want=$(jq -r .status <<< "$case")
  says=$(jq -r '.says // empty' <<< "$case")
  why=
  if [[ $status != "$want" ]]; then
    why="the status is $status, not $want"
  elif [[ -n $says && $(< "$dir/err") != *"$says"* ]]; then
    why="stderr holds no line with \"$says\""
  elif [[ $want != 0 && -e $dir/ran ]]; then
    why="the check runs, although the replay refuses the tree"
  fi
  if [[ -n $why ]]; then
    printf 'replay environment case FAILED: %s: %s\n' "$name" "$why" >&2
    sed 's/^/    /' "$dir/err" >&2
    failed=1
  fi
done
(( failed == 0 )) || exit 1
echo "replay environments OK: $count cases run each check in the environment of the tree that it reads"
