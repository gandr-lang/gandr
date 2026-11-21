#!/usr/bin/env bash
# Lints a pull request title. The direct form runs before an opening. The
# numbered form reads the title as it stands before a landing. A re-run reads
# the title from the API rather than from its event.
# - see: #5777
#
# The read of the title runs apart from commitlint. A pipe from the read into
# commitlint loses the read's failure. In run 43058991759 the answer is no
# JSON, `gh`'s `--jq` fails, and commitlint reports no input (#6774). So a
# failed read stops here with its own line. Commitlint lints only a title that
# the read gives.
#
# Usage: lint.bash --title <title>, or lint.bash <number> with
# `GITHUB_REPOSITORY` and `GH_TOKEN` set. Exits 1 on a failed read or a
# refused title.
set -euo pipefail
title=
if [[ ${1:-} == --title ]]; then
  [[ $# == 2 ]] || { echo 'usage: lint.bash --title <title>' >&2; exit 2; }
  title=$2
else
  number=${1:?usage: lint.bash --title <title> | <number>}
  repo=${GITHUB_REPOSITORY:?GITHUB_REPOSITORY names the repository}
  error=$(mktemp)
  trap 'rm -f "$error"' EXIT
  if ! title=$(gh api "repos/$repo/pulls/$number" --jq .title 2> "$error"); then
    printf 'the read of the title of #%s failed: %s\n' "$number" "$(< "$error")" >&2
    exit 1
  fi
  if [[ -z $title ]]; then
    printf 'the read of the title of #%s gave no title\n' "$number" >&2
    exit 1
  fi
fi
printf '%s\n' "$title" | COMMITLINT_TITLE=1 mise exec -- commitlint
