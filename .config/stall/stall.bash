# The stall detector's reading (#2785), sourced by `stall:check` and
# `stall:watch`. It reads the open pull requests in one query and decides
# with `detect.jq`; it queues, revises and comments nothing.
#
# The thresholds are `defaults.json`'s, each overridden by the configuration's
# `thresholds`. The configuration and the detector's memory live outside the
# tree, under the XDG directories:
#   $XDG_CONFIG_HOME/gandr/stall.json   `{thresholds?, lanes?, page?}`;
#       `lanes` the lanes a finding is placed in (absent, every lane), and
#       `page` `{command, triage, coordinator, seats?, check?}`: the page
#       script's argument vector, then each target's arguments before the
#       line (a seat's name, which the page script resolves, #2977), `seats`
#       each lane's seat's by the lane (#2972), `check` the command that
#       exits 0 when a seat, its arguments appended, has a live block;
#   $XDG_STATE_HOME/gandr/stall.json    `{seen, paged, stalled}`, `detect.jq`'s,
#       and `gone`, `stall:watch`'s count of readings each seat was found
#       without a live block.

stall_dir="$(git rev-parse --show-toplevel)/.config/stall"
stall_config="${XDG_CONFIG_HOME:-$HOME/.config}/gandr/stall.json"
stall_state="${XDG_STATE_HOME:-$HOME/.local/state}/gandr/stall.json"
source "$stall_dir/../claims/deps.bash"

# The configuration, `{}` when there is none.
stall_configuration() {
  if [[ -f "$stall_config" ]]; then jq -c . "$stall_config"; else echo '{}'; fi
}

# The thresholds: the defaults, each overridden by the configuration's.
stall_thresholds() {
  jq -c --argjson config "$(stall_configuration)" '. * ($config.thresholds // {})' "$stall_dir/defaults.json"
}

# One reading of the repository `$1` (owner/name) against its trunk `$2`, with
# the memory `$3` (`{seen, paged}`): `detect.jq`'s answer. The lanes a seat
# holds are the configuration's `page.seats`, each lane's areas
# `.config/issues/lanes.toml`'s (#3822). The programme focus is `deps_focus`'s,
# its open members no seat owns (#3959). Fails, printing nothing on stdout,
# when a read fails.
stall_reading() {
  local repo=$1 trunk=$2 memory=$3 required raw areas focus
  required=$(gh api "repos/$repo/rules/branches/$trunk" \
    --jq '[.[] | select(.type == "required_status_checks") | .parameters.required_status_checks[].context] | unique') || return 1
  raw=$(gh api graphql -F owner="${repo%/*}" -F name="${repo#*/}" -F query=@"$stall_dir/query.graphql") || return 1
  areas=$(yq -p toml -o json -I 0 '.lane' "$stall_dir/../issues/lanes.toml") || return 1
  focus=$(deps_focus "$repo" | jq -c 'if . == null then null else {epics, open: [.members[]
    | select(.state == "open" and any(.labels[]; IN("kind:epic", "status:claimed", "status:deferred", "status:discarded")) == false)
    | .number]} end') || return 1
  jq -c '.data.repository' <<< "$raw" | jq -c -L "$stall_dir/../claims" -f "$stall_dir/facts.jq" \
    | jq -c --argjson now "$(date +%s)" --arg trunk "$trunk" --argjson required "$required" \
      --argjson thresholds "$(stall_thresholds)" --argjson config "$(stall_configuration)" --argjson memory "$memory" \
      --argjson areas "$areas" --argjson focus "$focus" \
      '{now: $now, trunk: $trunk, required: $required, thresholds: $thresholds, lanes: $config.lanes, prs: .prs, merged: .merged, filed: .filed, claimed: .claimed, seats: ($config.page.seats // {} | keys), areas: $areas, focus: $focus, seen: $memory.seen, paged: $memory.paged, stalled: $memory.stalled}' \
    | jq -c -f "$stall_dir/detect.jq"
}

# The memory the last reading left, `{}` when there is none.
stall_memory() {
  if [[ -f "$stall_state" ]]; then jq -c . "$stall_state"; else echo '{}'; fi
}
