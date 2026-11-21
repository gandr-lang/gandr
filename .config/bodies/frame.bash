# shellcheck shell=bash
# The version of the unit frame (#7018), sourced by `unit:frame`,
# `unit:sign`, `issue:file` and `claim:take`. `unit_frame <root>` prints one
# digest of the rows that
# `units.md` asks of a unit: the axes and their questions (`sections.jq`) and
# the concerns of `ledger/concerns.sql`. A change of a row gives a new
# digest. The digest is the first 12 hex digits of the git object name of
# their canonical JSON, the same on each host. `unit_frame <root> kept`
# prints the digest of the frame without the axes of `noted_axes` (#7350):
# the frame that a unit signed before those axes answers, byte for byte.
unit_frame() {
  local root=$1 concerns
  concerns=$(sqlite3 -json :memory: ".read $root/ledger/concerns.sql" 'SELECT id FROM concern ORDER BY id;')
  jq -n -S -c -L "$root/.config/bodies" --argjson concerns "$concerns" --arg form "${2:-now}" \
    'include "sections";
     (if $form == "kept" then noted_axes else [] end) as $gone
     | {axes: [axes[] | select(IN($gone[]) | not)], questions: (questions | delpaths([$gone[] | [.]])), concerns: [$concerns[].id]}' \
    | git hash-object --stdin | awk '{ print substr($1, 1, 12) }'
}

# The marker that `unit:sign` writes on the issue: the frame's digest in an
# HTML comment, which `claim:take` reads at a claim (#7018).
unit_frame_marker() {
  printf '<!-- signed frame=%s -->\n' "$1"
}

# `unit_frame_signoff` signs issue `$2` at the current frame of tree `$1`.
# It writes one comment with the frame marker and signer `$3`.
# `unit:sign` writes the comment after it adds `shape:signed`.
# `issue:file` writes it only after a mechanically sufficient `unit:check`.
# `claim:take` then takes the unit.
# - see: #7545, #7598, #7129
unit_frame_signoff() {
  local root=$1 number=$2 signer=$3 frame
  frame=$(unit_frame "$root")
  gh issue comment "$number" --body "$(unit_frame_marker "$frame")
$signer signs the sections at the unit frame \`$frame\`." > /dev/null
  printf '%s\n' "$frame"
}

# `{marker, frame, kept}` for issue `$3` of repository `$2`: the digest of
# its newest frame marker, or null for none, the frame's digest now at the
# tree `$1`, and the digest of the frame without the noted axes, which a
# unit signed before them still answers (#7350). One REST read of the
# issue's comments, in pages of 100. Fails when the read or a digest fails,
# so the claim refuses (`taken.jq`).
unit_frame_signed() {
  local root=$1 repo=$2 number=$3 frame kept markers
  frame=$(unit_frame "$root")
  kept=$(unit_frame "$root" kept)
  markers=$(gh api "repos/$repo/issues/$number/comments?per_page=100" --paginate \
    --jq '.[].body | capture("<!-- signed frame=(?<digest>[0-9a-f]+) -->").digest')
  jq -nc --arg frame "$frame" --arg kept "$kept" --arg markers "$markers" \
    '{marker: ($markers | split("\n") | map(select(. != "")) | last), frame: $frame, kept: $kept}'
}

# Page the architect once for issue `$1` refused at the frame `$2`, with the
# line `$3`. The page command is the stall watcher's (`stall.json`'s
# `page.command`), and the seat is its `page.seats.architect`, else
# `architect`. A state file for each issue and frame keeps a second refusal
# from paging again. A host with no page command prints that it pages no one.
unit_frame_page() {
  local number=$1 frame=$2 line=$3 config state
  config=${XDG_CONFIG_HOME:-$HOME/.config}/gandr-factory/stall.json
  state=${XDG_STATE_HOME:-$HOME/.local/state}/gandr-factory/frame-paged
  [[ ! -e $state/$number-$frame ]] || return 0
  local -a command seat
  if [[ -f $config ]]; then
    mapfile -t command < <(jq -r '(.page.command // [])[]' "$config")
    mapfile -t seat < <(jq -r '(.page.seats.architect // ["architect"])[]' "$config")
  fi
  if (( ${#command[@]} == 0 )); then
    echo "claim:take: no page command in $config, so no page reaches the architect for #$number" >&2
    return 0
  fi
  "${command[@]}" "${seat[@]}" "$line" || return 0
  mkdir -p "$state" && : > "$state/$number-$frame"
}
