#!/usr/bin/env bash
# The input `claim:next` gives `next.jq` (#5292, `input.bash`), run by
# `check:claims`. Each reading is longer than the 131072 bytes that Linux
# allows one argument, and the input carries each reading whole.
set -euo pipefail
source "$(cd "${BASH_SOURCE[0]%/*}" && pwd)/input.bash"
dir=$(mktemp -d)
trap 'rm -rf "$dir"' EXIT
failed=0

fail() {
  echo "input case FAILED: $1"
  echo "  got: $2"
  failed=1
}

for reading in "${claim_readings[@]}"; do
  jq -n --arg reading "$reading" '{reading: $reading, pad: ("x" * 140000)}' > "$dir/$reading.json"
done
got=$(claim_input "$dir" workflow 7 \
  | jq -c '[$ARGS.positional[] as $r | if .[$r].reading == $r and (.[$r].pad | length) == 140000 then empty else $r end]
      + [.lane, .now, (keys | length)]' --args "${claim_readings[@]}")
[[ $got == "[\"workflow\",7,$(( ${#claim_readings[@]} + 2 ))]" ]] \
  || fail "#5292: each reading past the argument limit reaches next.jq whole, beside the lane and the time" "$got"

(( failed == 0 )) || exit 1
echo "input check OK: ${#claim_readings[@]} readings past the argument limit read whole"
