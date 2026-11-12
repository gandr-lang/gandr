# shellcheck shell=bash
# The scaling account of `gandr check` (#6879), sourced by `bench:scaling`.
# Each pass reads the head of `main` and the open account. It measures a head
# that the account does not hold on the wide host, through the host's measure
# command, and writes the head's row (`account.jq`). A row whose widest
# speed-up falls by the configured share opens one defect through the
# `scaling-fall` template.
#
# The configuration and the memory live outside the tree, under the XDG
# directories:
#   $XDG_CONFIG_HOME/gandr/scaling.json   `{measure, widths, placement,
#       interval, share, page}`: the measure command's argument vector before
#       its own arguments, the points of the curve and of the placement as
#       `{threads, nodes}`, the seconds between passes, the share of a fall,
#       and the page command's argument vector before the line;
#   $XDG_STATE_HOME/gandr/scaling.json    `{paged}`: the keys of the pages
#       already sent.
#
# The measure command takes `<head> curve <paths>`, `<head> <nodes> gandr
# <arguments>` and `<head> <nodes> bench <cargo bench arguments>`. It builds
# the head on the wide host, holds that host's measurement lock, and prints
# what `curve.jq` and `run.jq` read.
#
# The task sets `config`, the configuration, and `scratch`, its scratch
# directory, before it calls a function here.
# shellcheck disable=SC2154

scaling_dir="$(git rev-parse --show-toplevel)/.config/bench"
scaling_config="${XDG_CONFIG_HOME:-$HOME/.config}/gandr/scaling.json"
scaling_state="${XDG_STATE_HOME:-$HOME/.local/state}/gandr/scaling.json"
scaling_title="perf: the scaling account of gandr check"
# The roots that the curve checks: those of `check:corpus`.
scaling_paths=(crates/surface-corpus/strict library/std)
# The most characters that the account's body holds.
scaling_limit=60000

# The configuration, or nothing on stdout and exit 2 when it is missing or
# malformed.
scaling_configuration() {
  if [[ -f "$scaling_config" ]] && jq -e '(.measure | type == "array" and length > 0 and all(type == "string"))
      and (.widths | type == "array" and length > 1 and all(.threads > 0 and (.nodes | type == "string")))
      and (.placement.threads > 0 and (.placement.nodes | type == "string"))
      and (.interval | type == "number" and . > 0)
      and (.share | type == "number" and . > 0 and . < 1)
      and (.page | type == "array" and length > 0 and all(type == "string"))' "$scaling_config" > /dev/null; then
    jq -c . "$scaling_config"
    return
  fi
  echo "bench:scaling reads $scaling_config: {\"measure\": [<command>, ...], \"widths\": [{\"threads\": 1, \"nodes\": \"0\"}, ...], \"placement\": {\"threads\": 16, \"nodes\": \"0-1\"}, \"interval\": <seconds>, \"share\": <fraction>, \"page\": [<page script>, ...]}" >&2
  return 2
}

# Page the line `$2` once under the key `$1`, as `follow_page` does: a key
# already paged sends nothing, and the memory keeps the last 32 keys.
scaling_page() {
  local key=$1 line=$2 memory page
  memory=$(if [[ -f "$scaling_state" ]]; then jq -c . "$scaling_state"; else echo '{}'; fi)
  echo "$line" >&2
  if jq -e --arg key "$key" '(.paged // []) | index($key)' <<< "$memory" > /dev/null; then return 0; fi
  mapfile -t page < <(jq -r '.page[]' <<< "$config")
  "${page[@]}" "$line" || return 0
  mkdir -p "$(dirname "$scaling_state")"
  jq -c --arg key "$key" '.paged = ((.paged // []) + [$key])[-32:]' <<< "$memory" > "$scaling_state.tmp"
  mv "$scaling_state.tmp" "$scaling_state"
}

# Run the measure command with the arguments `$@`, its output in
# `$scratch/out`. Exit with the command's status.
scaling_run() {
  local measure
  mapfile -t measure < <(jq -r '.measure[]' <<< "$config")
  "${measure[@]}" "$@" > "$scratch/out" 2>&1
}

# Measure the head `$1` and print its row for `account.jq`, or print the
# reason on stderr and exit 1. `$scratch` is the task's scratch directory.
scaling_measure() {
  local head=$1 out=$scratch/out widths curve walls threads nodes hotpath run status
  widths=$(jq -c .widths <<< "$config")
  status=0
  scaling_run "$head" curve "${scaling_paths[@]}" || status=$?
  if ! curve=$(jq -R -s -c --argjson widths "$widths" -f "$scaling_dir/curve.jq" < "$out" 2>&1) || (( status != 0 )); then
    echo "the curve exits $status: $(awk 'NF {line = $0} END {print line}' "$out"); $curve" >&2
    return 1
  fi
  threads=$(jq -r .placement.threads <<< "$config")
  nodes=$(jq -r .placement.nodes <<< "$config")
  walls='[]'
  for _ in 1 2 3; do
    status=0
    scaling_run "$head" "$nodes" gandr check --recheck -j "$threads" "${scaling_paths[@]}" || status=$?
    if ! run=$(jq -R -s -c -f "$scaling_dir/run.jq" < "$out" 2>&1) || (( status != 0 )); then
      echo "the placement at $threads threads on $nodes exits $status: $run" >&2
      return 1
    fi
    walls=$(jq -c --argjson run "$run" '. + [$run.wall]' <<< "$walls")
  done
  status=0
  scaling_run "$head" "$(jq -r '.[0].nodes' <<< "$widths")" bench -p gandr-lang --bench hotpath --features hotpath --no-run || status=$?
  (( status == 0 )) || { echo "the hotpath series does not build: $(awk 'NF {line = $0} END {print line}' "$out")" >&2; return 1; }
  hotpath='[]'
  while IFS=$'\t' read -r threads nodes; do
    status=0
    scaling_run "$head" "$nodes" bench -p gandr-lang --bench hotpath --features hotpath -- --jobs "$threads" || status=$?
    if ! run=$(jq -R -s -c -f "$scaling_dir/run.jq" < "$out" 2>&1) || (( status != 0 )); then
      echo "the hotpath series at $threads threads on $nodes exits $status: $run" >&2
      return 1
    fi
    hotpath=$(jq -c --argjson run "$run" '. + [{wall: $run.wall}]' <<< "$hotpath")
  done < <(jq -r '.[] | "\(.threads)\t\(.nodes)"' <<< "$widths")
  jq -n -c --argjson curve "$curve" --argjson walls "$walls" --argjson hotpath "$hotpath" --arg date "$(git show -s --format=%cs "$head")" \
    '{head: $curve.commit, date: $date, load: $curve.load, points: $curve.points,
      placement: {median: ($walls | sort | .[1])}, hotpath: $hotpath, defect: null}'
}

# The account's body for the row `$1` with the defect `$2` (or `null`), from
# the account `$3` as `issue_found` gives it, and the closed defects `$4`.
scaling_account() {
  jq -n -c --argjson row "$1" --argjson defect "$2" --argjson found "$3" --argjson closed "$4" \
    --argjson config "$config" --argjson limit "$scaling_limit" \
    --argjson paths "$(printf '%s\n' "${scaling_paths[@]}" | jq -R . | jq -s -c .)" \
    '{body: ($found.body // null), row: ($row + {defect: $defect}), widths: $config.widths,
      placement: $config.placement, paths: $paths, share: $config.share, limit: $limit, closed: $closed}' \
    | jq -c -f "$scaling_dir/account.jq"
}

# One pass: measure the head `$1`, or the head of `main` when it is empty, and
# write its row. With `$2` set, print the body, the moved rows and the fall,
# and write nothing. `$scratch` is the task's scratch directory.
scaling_once() {
  local head=$1 print=$2 found number closed row account fall fields defect
  if [[ -z $head ]]; then
    git fetch -q origin main
    head=$(git rev-parse origin/main)
  else
    head=$(git rev-parse --verify "$head^{commit}")
  fi
  found=$(issue_found "$scaling_title")
  if [[ $(jq -r --arg head "${head:0:9}" '(.body // "") | contains("| `" + $head + "` |")' <<< "$found") == true && -z $print ]]; then
    echo "bench:scaling: the account holds ${head:0:9}"
    return 0
  fi
  echo "bench:scaling: measuring ${head:0:9}"
  if ! row=$(scaling_measure "$head"); then
    scaling_page "measure:$head" "SCALING measure-failed: the wide host does not measure main at ${head:0:9}; the service log names the step"
    return 1
  fi
  # The defects of open falls that closed since the last pass.
  closed='[]'
  for number in $(jq -r '(.body // "") | [scan("\\| fall: #([0-9]+) \\|")[0]] | unique[]' <<< "$found"); do
    if [[ $(gh issue view "$number" --json state --jq .state) == CLOSED ]]; then
      closed=$(jq -c --argjson n "$number" '. + [$n]' <<< "$closed")
    fi
  done
  account=$(scaling_account "$row" null "$found" "$closed")
  fall=$(jq -c .fall <<< "$account")
  if [[ -n $print ]]; then
    jq -r '.body, (.moved // empty), (.fall // empty | tojson)' <<< "$account"
    return 0
  fi
  if [[ $fall != null ]]; then
    fields=$(jq -c 'del(.table)' <<< "$fall")
    jq -r '"## Observation\n\nThe scaling account reads a fall of the speed-up at its widest point in these two rows.\n\n" + .table' <<< "$fall" > "$scratch/observation.md"
    defect=$(mise run --quiet issue:file "perf: the speed-up of gandr check at $(jq -r .threads <<< "$fall") threads falls $(jq -r .drop <<< "$fall") % at $(jq -r .head <<< "$fall")" \
      "$scratch/observation.md" kind:defect area:core --template scaling-fall --fields "$fields" \
      | sed -n 's|.*/issues/\([0-9][0-9]*\)$|\1|p' | tail -n 1)
    account=$(scaling_account "$row" "${defect:-null}" "$found" "$closed")
  fi
  jq -r .body <<< "$account" > "$scratch/body.md"
  issue_keep "$scaling_title" "$found" 1 "$scratch/body.md" \
    mise run --quiet issue:file "$scaling_title" "$scratch/body.md" kind:performance area:workflow collector
  if [[ $(jq -r '.moved // empty' <<< "$account") != "" ]]; then
    jq -r .moved <<< "$account" > "$scratch/moved.md"
    gh issue comment "$(jq -r .number <<< "$found")" --body-file "$scratch/moved.md" > /dev/null
  fi
}
