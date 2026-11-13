# The input `pr:open` gives `opening.jq` (#7076), sourced by `pr:open`. Each
# reading is one JSON file in the run's directory, and jq reads it through
# `--slurpfile`, never as an argument. Linux refuses one argument longer than
# 131072 bytes, and the readings grow with the change past that limit: the
# regressions of a change that moves test files, as one case.
opening_readings=(issues mentions concerns added regressions surface ceilings budget comments vault)

# opening_input <dir> <branch> <body>: the input object of `opening.jq`, each
# reading read from `<dir>/<reading>.json` and the body from the file <body>.
opening_input() {
  local dir=$1 branch=$2 body=$3 reading
  local files=()
  for reading in "${opening_readings[@]}"; do
    files+=(--slurpfile "$reading" "$dir/$reading.json")
  done
  jq -n "${files[@]}" --arg branch "$branch" --rawfile body "$body" \
    '($ARGS.named | del(.branch, .body) | map_values(.[0])) + {branch: $branch, body: $body}'
}
