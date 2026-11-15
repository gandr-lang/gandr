# The stall detector's reading (#2785), sourced by `stall:check` and
# `stall:watch`. It reads the open pull requests in one query and decides
# with `detect.jq`; it queues, revises and comments nothing.
#
# The thresholds are `defaults.json`'s, each overridden by the configuration's
# `thresholds`. The configuration and the detector's memory live outside the
# tree, under the XDG directories:
#   $XDG_CONFIG_HOME/gandr/stall.json   `{thresholds?, lanes?, page?}`;
#       `lanes` the lanes a finding is placed in (absent, every lane), and
#       `page` `{command, triage, coordinator, seats?, check?, activity?,
#       claim?, peek?}`: the page script's argument vector, then each target's
#       arguments before the line (a seat's name, which the page script
#       resolves, #2977), `seats` each lane's seat's by the lane (#2972),
#       `check` the command that exits 0 when a seat, its arguments appended,
#       has a live block, `activity` the command that prints a seat's
#       activity record, its arguments appended (#5996), and `claim` and
#       `peek` the claim command and its dry run, each `{lane}` the lane's
#       name: `claim` is named in a seat's idle page, and `peek` exits 0 and
#       prints the work that `claim` would give;
#   $XDG_CONFIG_HOME/gandr/hold         each held lane first on its line, or
#       `*` for every lane, then the reason: a held lane holds no seat for
#       the reading, so it is never idle, and its pull requests are still read;
#   $XDG_STATE_HOME/gandr/stall.json    `{seen, paged, stalled}`, `detect.jq`'s,
#       `gone`, `stall:watch`'s count of readings each seat was found
#       without a live block, `activity` each seat's last activity record by
#       its lane, and `read`, the time of its last reading.

stall_dir="$(git rev-parse --show-toplevel)/.config/stall"
stall_config="${XDG_CONFIG_HOME:-$HOME/.config}/gandr/stall.json"
stall_hold="${XDG_CONFIG_HOME:-$HOME/.config}/gandr/hold"
stall_state="${XDG_STATE_HOME:-$HOME/.local/state}/gandr/stall.json"
stall_home="${XDG_STATE_HOME:-$HOME/.local/state}/gandr/stall-service"
source "$stall_dir/../issues/deps.bash"
source "$stall_dir/../claims/lanes.bash"
source "$stall_dir/../service/service.bash"

# The configuration, `{}` when there is none.
stall_configuration() {
  if [[ -f "$stall_config" ]]; then jq -c . "$stall_config"; else echo '{}'; fi
}

# The held lanes as a JSON array, `["*"]` when every lane is held, `[]` when
# none is.
stall_held() {
  if [[ -f "$stall_hold" ]]; then awk 'NF { print $1 }' "$stall_hold" | jq -R -s -c 'split("\n") | map(select(. != ""))'; else echo '[]'; fi
}

# The thresholds: the defaults, each overridden by the configuration's.
stall_thresholds() {
  jq -c --argjson config "$(stall_configuration)" '. * ($config.thresholds // {})' "$stall_dir/defaults.json"
}

# Each seat's activity by its lane (#5996): the `page.activity` command's
# record for the lane's seat, `{state, since, line}`. The seats are read at
# once, each in its own process. A read that fails, or prints no record,
# keeps the lane's activity from the memory `$1`; a lane with neither is
# absent, and its activity is not known.
stall_activity() {
  local memory=$1 config activity lane out scratch
  local -a command args
  config=$(stall_configuration)
  activity=$(jq -c '.activity // {}' <<< "$memory")
  mapfile -t command < <(jq -r '(.page.activity // [])[]' <<< "$config")
  if (( ${#command[@]} == 0 )); then echo "$activity"; return; fi
  scratch=$(mktemp -d)
  while IFS= read -r lane; do
    mapfile -t args < <(jq -r --arg lane "$lane" '.page.seats[$lane][]' <<< "$config")
    { "${command[@]}" "${args[@]}" > "$scratch/$lane" 2> /dev/null || rm -f "$scratch/$lane"; } &
  done < <(jq -r '.page.seats // {} | keys[]' <<< "$config")
  wait
  for out in "$scratch"/*; do
    jq -e -s 'length == 1 and (.[0] | type) == "object" and (.[0].state | IN("working", "waiting", "idle")) and (.[0].since | type) == "number"' \
      "$out" > /dev/null 2>&1 || continue
    activity=$(jq -c --arg lane "${out##*/}" --slurpfile record "$out" '.[$lane] = $record[0]' <<< "$activity")
  done
  rm -rf "$scratch"
  echo "$activity"
}

# One reading of the repository `$1` (owner/name) against its trunk `$2`, with
# the memory `$3` (`{seen, paged, activity}`): `detect.jq`'s answer, with
# `activity`, each seat's activity, for the next memory. The lanes a seat
# holds are the configuration's `page.seats` that no hold names, each lane's
# areas the factory's lane table's (`../claims/lanes.bash`, #3822). Fails, printing nothing on
# stdout, when a read fails.
stall_reading() {
  local repo=$1 trunk=$2 memory=$3 required raw areas activity table
  required=$(gh api "repos/$repo/rules/branches/$trunk" \
    --jq '[.[] | select(.type == "required_status_checks") | .parameters.required_status_checks[].context] | unique') || return 1
  raw=$(gh api graphql --paginate -F owner='{owner}' -F name='{repo}' -F query=@"$stall_dir/query.graphql") || return 1
  table=$(lanes_file)
  areas=$(yq -p toml -o json -I 0 '.lane' "$table") || return 1
  activity=$(stall_activity "$memory")
  jq -cs '. as $pages | $pages[0].data.repository | .refactors.nodes = [$pages[] | (.data.repository.refactors.nodes // [])[]]' <<< "$raw" | jq -c -L "$stall_dir/../bodies" -L "$stall_dir/../claims" -f "$stall_dir/facts.jq" \
    | jq -c --argjson now "$(date +%s)" --arg trunk "$trunk" --argjson required "$required" \
      --argjson thresholds "$(stall_thresholds)" --argjson config "$(stall_configuration)" --argjson memory "$memory" \
      --argjson areas "$areas" --argjson held "$(stall_held)" --argjson activity "$activity" \
      '{now: $now, trunk: $trunk, required: $required, thresholds: $thresholds, lanes: $config.lanes, prs: .prs, merged: .merged, filed: .filed, claimed: .claimed, seats: ($config.page.seats // {} | keys | if ($held | index("*")) then [] else . - $held end), activity: $activity, claim: ($config.page.claim // null | if . == null then null else join(" ") end), areas: $areas, seen: $memory.seen, paged: $memory.paged, stalled: $memory.stalled}' \
    | jq -c -f "$stall_dir/detect.jq" | jq -c --argjson activity "$activity" '. + {activity: $activity}'
}

# The memory the last reading left, `{}` when there is none.
stall_memory() {
  if [[ -f "$stall_state" ]]; then jq -c . "$stall_state"; else echo '{}'; fi
}

# The detector's liveness (#4167): `live.jq`'s line when the last reading
# `stall:watch` recorded is older than two intervals or absent, else nothing.
stall_liveness() {
  stall_memory | jq -c --argjson now "$(date +%s)" --argjson interval "$(stall_thresholds | jq .interval)" \
    '{now: $now, interval: $interval, read: .read}' | jq -r -f "$stall_dir/live.jq"
}

# Install (`$1` = install) or remove (`$1` = remove) the service that keeps
# `stall:watch` running (#4167), through `.config/service/service.bash`. The
# service runs from a checkout of its own, `stall_home` under the state
# directory, which an install sets to `origin/landing` first (#7002).
stall_service() {
  if [[ $1 == install ]]; then
    service_home_sync "$stall_home" || { echo "stall:watch --install: $stall_home cannot take origin/landing" >&2; return 1; }
  fi
  (cd "$stall_home" 2> /dev/null || :; service_unit "$1" stall-watch stall:watch 'gandr stall detector (stall:watch)')
}

# Whether a move of the service's checkout from `$1` to its `HEAD` changes a
# file that `stall:watch` reads: one under `.config/` or `mise.toml`. The
# watch then starts again from the new scripts (#7002).
stall_scripts_moved() {
  ! git -C "$stall_home" diff --quiet "$1" HEAD -- .config mise.toml
}
