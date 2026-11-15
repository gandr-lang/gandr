#!/usr/bin/env bash
# Writes the body of each pull request that a CI run of `check:prose` reads
# (#7621), so the run reads their named overrides where `main` is decided.
# The pull requests are those whose number closes a commit subject from
# <base> to HEAD, as the queue's merge commits name them, and the pull
# request of the event when one is given. Prints the paths of the bodies,
# joined by `:`, for `PROSE_OVERRIDE`.
#
# Usage: bodies.bash <base> <dir> [<pull request>]
set -euo pipefail
base=${1:?usage: bodies.bash <base> <dir> [<pull request>]}
dir=${2:?usage: bodies.bash <base> <dir> [<pull request>]}
mkdir -p "$dir"
source "$(git rev-parse --show-toplevel)/.config/gh/budget.bash"
mapfile -t numbers < <({
  git log --format=%s "$base..HEAD" | sed -nE 's/.* \(#([0-9]+)\)$/\1/p'
  if [[ -n ${3:-} ]]; then echo "$3"; fi
} | sort -un)
paths=()
for number in "${numbers[@]}"; do
  gh pr view "$number" --json body --jq .body > "$dir/$number.md"
  paths+=("$dir/$number.md")
done
(IFS=:; echo "${paths[*]}")
