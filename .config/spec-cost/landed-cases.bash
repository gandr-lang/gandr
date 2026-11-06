#!/usr/bin/env bash
set -euo pipefail

work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-spec-cost-landed.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/landed"

actual=$(.config/spec-cost/landed.bash "$work/landed" "$work/plain")
expected='No enforcing shard reports were available for this landing.'
if [[ $actual != "$expected" ]]; then
  printf 'spec-cost landed report case failed\n  expected: %s\n  actual:   %s\n' "$expected" "$actual" >&2
  exit 1
fi

echo 'spec-cost landed report OK: an empty landed report directory writes a skip result'
