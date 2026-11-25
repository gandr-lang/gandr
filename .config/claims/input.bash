# The input `claim:next` gives `next.jq` (#5292), sourced by `claim:next`.
# Each reading is one JSON file in the run's board directory, and jq reads it
# through `--slurpfile`, never as an argument. Linux refuses one argument
# longer than 131072 bytes, and the board's readings grow past that limit
# (#2671).
claim_readings=(areas issues order refusals prs live lanes branches reread)

# claim_input <dir> <lane> <now>: the input object of `next.jq`, each reading
# read from `<dir>/<reading>.json`.
claim_input() {
  local dir=$1 lane=$2 now=$3 reading
  local files=()
  for reading in "${claim_readings[@]}"; do
    files+=(--slurpfile "$reading" "$dir/$reading.json")
  done
  jq -n "${files[@]}" --arg lane "$lane" --argjson now "$now" \
    '($ARGS.named | del(.lane, .now) | map_values(.[0])) + {lane: $lane, now: $now}'
}
