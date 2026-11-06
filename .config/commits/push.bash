#!/usr/bin/env bash
# The push tier's commit rules (#2640): the commits a pushed ref carries past
# the trunk, `origin/$trunk` (`.config/pr-stack/trunk.bash`, #5443), are
# linted (`lint.bash`) before they reach the server, where a
# trailer-less commit would fail the format gate and hold every pull request
# stacked above it. prek runs it at `pre-push` with the pushed commit in
# `PRE_COMMIT_TO_REF` and the remote ref in `PRE_COMMIT_REMOTE_BRANCH`. A
# deletion pushes no commit. Only a branch carries the tree's commits: a
# notes ref or a tag shares no history with the trunk, so no rule reads it
# (#5651). The script reads its siblings from its own directory, and takes a
# `COMMITLINT_BIN` set before it, so `check:commits` runs it in a scratch
# repository.
set -euo pipefail
head=${PRE_COMMIT_TO_REF:-}
[[ -n "$head" && ! "$head" =~ ^0+$ ]] || exit 0
[[ ${PRE_COMMIT_REMOTE_BRANCH:-refs/heads/} == refs/heads/* ]] || exit 0
here=$(dirname "${BASH_SOURCE[0]}")
COMMITLINT_BIN=${COMMITLINT_BIN:-$(mise which commitlint)}
export COMMITLINT_BIN
source "$here/../pr-stack/trunk.bash"
exec "$here/lint.bash" "$(git merge-base "origin/$trunk" "$head")" "$head"
