#!/usr/bin/env bash
# The commit rules over the authored commits of each entry that a merge group
# lands (#6883). The gate of `pr:open` lints a branch's commits on the lane's
# host, and nothing read them where they land. The queue of `landing` groups
# by `HEADGREEN`, so a green group lands every entry below it (#6839): each
# entry's commits are read, never those of `HEAD` alone. An entry's commits
# are the commits that its head holds and its merge's first parent does not,
# each linted by `.config/commits/lint.bash` as the gate lints it.
#
# `<entries>` is the output of `.config/queue/entries.bash`. With
# `--fetch <rev>`, a shallow checkout first deepens `<rev>` until each
# entry's head meets its merge's first parent, 10 commits at a time and 5
# times at most. An entry whose head meets it in none is refused.
#
# Usage: commits.bash [--fetch <rev>] <entries>
# Exits 1 when a commit fails the rules and 2 when an entry's history does
# not read; it reads every entry before it exits.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
fetch=
if [[ ${1:-} == --fetch ]]; then fetch=${2:?--fetch takes a revision}; shift 2; fi
entries=${1:?usage: commits.bash [--fetch <rev>] <entries>}
# The commit rules read each commit's own author; a title's mode has none.
unset COMMITLINT_TITLE
COMMITLINT_BIN=${COMMITLINT_BIN:-$(mise which commitlint)}
export COMMITLINT_BIN
met() { git merge-base "$1^1" "$2" > /dev/null 2>&1; }
status=0
worst() { (( $1 > status )) && status=$1 || :; }
while read -r merge number head; do
  echo "pull request #$number at ${head:0:9}:"
  if [[ -n $fetch ]]; then
    for _ in 1 2 3 4 5; do
      met "$merge" "$head" && break
      git fetch --quiet --no-tags --deepen=10 origin "$fetch"
    done
  fi
  if ! met "$merge" "$head"; then
    echo "queue: the head of pull request #$number does not meet its merge's first parent" >&2
    worst 2
    continue
  fi
  code=0
  "$here/../commits/lint.bash" "$merge^1" "$head" < /dev/null || code=$?
  worst "$code"
done < "$entries"
exit "$status"
