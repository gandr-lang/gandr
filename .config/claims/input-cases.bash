#!/usr/bin/env bash
# The inputs `claim:next` gives `next.jq` (#5292, `input.bash`) and `pr:open`
# gives `opening.jq` (#7076, `opening-input.bash`), run by `check:claims`.
# Each reading is longer than the 131072 bytes that Linux allows one
# argument, and the input carries each reading whole.
set -euo pipefail
source "$(cd "${BASH_SOURCE[0]%/*}" && pwd)/input.bash"
source "$(cd "${BASH_SOURCE[0]%/*}" && pwd)/../bodies/opening-input.bash"
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

for reading in "${opening_readings[@]}"; do
  jq -n --arg reading "$reading" '{reading: $reading, pad: ("x" * 140000)}' > "$dir/$reading.json"
done
printf 'Closes #7076.\n' > "$dir/body.md"
got=$(opening_input "$dir" triage-7076-files "$dir/body.md" \
  | jq -c '[$ARGS.positional[] as $r | if .[$r].reading == $r and (.[$r].pad | length) == 140000 then empty else $r end]
      + [.branch, .body, (keys | length)]' --args "${opening_readings[@]}")
[[ $got == "[\"triage-7076-files\",\"Closes #7076.\\n\",$(( ${#opening_readings[@]} + 2 ))]" ]] \
  || fail "#7076: each reading past the argument limit reaches opening.jq whole, beside the branch and the body" "$got"

(( failed == 0 )) || exit 1
echo "input check OK: ${#claim_readings[@]} readings of claim:next and ${#opening_readings[@]} of pr:open past the argument limit read whole"
