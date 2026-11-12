#!/usr/bin/env bash
# Lints the title of one pull request as it stands. A re-run repeats its
# event, so the title comes from the API and not from the event (#5777).
#
# The read of the title runs apart from commitlint. A pipe from the read into
# commitlint loses the read's failure. In run 43058991759 the answer is no
# JSON, `gh`'s `--jq` fails, and commitlint reports no input (#6774). So a
# failed read stops here with its own line. Commitlint lints only a title that
# the read gives.
#
# Usage: lint.bash <number>, with `GITHUB_REPOSITORY` and `GH_TOKEN` set.
# Exits 1 on a failed read or a refused title.
set -euo pipefail
number=${1:?usage: lint.bash <number>}
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
printf '%s\n' "$title" | mise exec -- commitlint
