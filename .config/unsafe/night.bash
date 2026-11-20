#!/usr/bin/env bash
# The night's choice of the crates that hold `unsafe` to check
# (`nightly-sweeps.yml`'s `freshness`, #7642): each crate of
# `.config/unsafe/crates.json` with a file that moved since the commit that the
# checks last covered.
#
#   .config/unsafe/night.bash <last successful run> <night's commit> <runner>
#
# A successful night records the commit that the checks cover as its artifact
# `unsafe-commit`. The checks run on a runner of our own alone. So a night on
# the hosted runner checks no crate and records the last commit again, and the
# next night on our runner checks what moved since then. Every crate of the
# list moved when no night recorded a commit, when GitHub gives no comparison,
# or when the comparison holds 300 files, the most that GitHub lists.
#
# The script writes the step's output `crates`, the commit to record in
# `$RUNNER_TEMP/unsafe/commit`, and one line of the step's summary.
set -euo pipefail
# shellcheck source=../gh/budget.bash
source "${BASH_SOURCE[0]%/*}/../gh/budget.bash"
run=${1:-}
night=${2:?the commit of the night}
runner=${3:?the runner of the night}
list=$(dirname "$0")/crates.json
last=
if [[ -n $run ]] && gh run download "$run" --name unsafe-commit --dir "$RUNNER_TEMP/unsafe-last"; then
  last=$(<"$RUNNER_TEMP/unsafe-last/commit")
fi
mkdir -p "$RUNNER_TEMP/unsafe"
if [[ $runner != integration ]]; then
  if [[ -n $last ]]; then
    printf '%s\n' "$last" > "$RUNNER_TEMP/unsafe/commit"
  fi
  printf 'crates=\n' >> "$GITHUB_OUTPUT"
  # shellcheck disable=SC2016 # The backquotes are Markdown of the summary.
  printf 'The night checks no crate that holds `unsafe`, since the checks run on a runner of our own alone. The checks last covered `%s`.\n' \
    "${last:-none}" >> "$GITHUB_STEP_SUMMARY"
  exit 0
fi
moved=$RUNNER_TEMP/unsafe/moved.json
printf 'null\n' > "$moved"
if [[ -n $last ]]; then
  gh api "repos/$GH_REPO/compare/$last...$night" --jq '[.files[].filename]' > "$moved" || printf 'null\n' > "$moved"
fi
crates=$(jq -r --slurpfile moved "$moved" '$moved[0] as $files
  | .crates
  | if $files == null or ($files | length) >= 300 then .
    else map(select(.path as $path | any($files[]; startswith($path + "/")))) end
  | map(.package) | join(" ")' "$list")
printf '%s\n' "$night" > "$RUNNER_TEMP/unsafe/commit"
printf 'crates=%s\n' "$crates" >> "$GITHUB_OUTPUT"
# shellcheck disable=SC2016 # The backquotes are Markdown of the summary.
printf 'The night checks the crates that hold `unsafe` with a file that moved since `%s`: %s.\n' \
  "${last:-none}" "${crates:-none}" >> "$GITHUB_STEP_SUMMARY"
