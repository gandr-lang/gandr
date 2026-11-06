#!/usr/bin/env bash
# An invalid cases file stops before the runner starts its absent program.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
fail() {
  printf 'cases check FAILED: %s\n' "$1" >&2
  exit 1
}
refuse() {
  local cases=$1
  local reading=$2
  local stderr="$scratch/stderr"
  local status
  if "$here/run.bash" cases "$cases" --program "$scratch/absent.jq" > /dev/null 2> "$stderr"; then
    status=0
  else
    status=$?
  fi
  (( status == 2 )) || fail "#5646: $reading exits $status, not 2"
  [[ $(< "$stderr") == *"$cases"* ]] || fail "#5646: $reading error does not name it"
}
malformed="$scratch/malformed.json"
not_array="$scratch/not-array.json"
printf '[\n  { "name": "before" }\n  }\n]\n' > "$malformed"
printf '{}\n' > "$not_array"
refuse "$malformed" "a malformed cases file"
refuse "$not_array" "a non-array cases file"
echo "cases check OK: runner refuses 2 invalid cases files before it runs a program"
