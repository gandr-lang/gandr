#!/usr/bin/env bash
# The push tier's commit rules (#2640): the commits a pushed ref carries past
# `origin/main` are linted (`lint.bash`) before they reach the server, where a
# trailer-less commit would fail the format gate and hold every pull request
# stacked above it. prek runs it at `pre-push` with the pushed commit in
# `PRE_COMMIT_TO_REF`; a deletion pushes no commit.
set -euo pipefail
head=${PRE_COMMIT_TO_REF:-}
[[ -n "$head" && ! "$head" =~ ^0+$ ]] || exit 0
COMMITLINT_BIN=$(mise which commitlint)
export COMMITLINT_BIN
exec "$(git rev-parse --show-toplevel)/.config/commits/lint.bash" "$(git merge-base origin/main "$head")" "$head"
