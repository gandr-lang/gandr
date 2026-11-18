#!/usr/bin/env bash
set -euo pipefail

reports=${1:?}
plain=${2:?}
found=false
age=

for report in "$reports"/junit-cargo-test-enforcing-shard-*/ci-enforcing/junit.xml; do
  [[ -f $report ]] || continue
  if [[ $found == false ]]; then
    age=$(( ($(date +%s) - $(date -d "${CI_BASELINE_CREATED:?}" +%s)) / 3600 ))
    found=true
  fi
  shard=${report#"$reports"/junit-cargo-test-enforcing-shard-}
  shard=${shard%%/*}
  printf '## %s\n\n' "$shard"
  mise run ci:spec-cost-ratio --plain "$plain" --enforcing "$report" --baseline-commit "${CI_BASELINE_SHA:?}" --baseline-age-hours "$age"
  printf '\n'
done

if [[ $found == false ]]; then
  printf 'No enforcing shard reports were available for this landing.\n'
fi
