#!/usr/bin/env bash
set -euo pipefail

work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-spec-cost-landed.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/landed"

fail() {
  printf '%s\n' "$1" >&2
  exit 1
}

actual=$(.config/spec-cost/landed.bash "$work/landed" "$work/plain")
expected='No enforcing shard reports were available for this landing.'
if [[ $actual != "$expected" ]]; then
  fail "#5496: expected $expected; got $actual"
fi

echo 'spec-cost landed report OK: an empty landed report directory writes a skip result'
