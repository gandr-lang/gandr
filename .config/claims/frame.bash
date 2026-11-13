# shellcheck shell=bash
# The version of the unit frame (#7018), sourced by `unit:frame` and
# `unit:sign`. `unit_frame <root>` prints one digest of the rows that
# `units.md` asks of a unit: the nine axes and their questions
# (`sections.jq`) and the concerns of `ledger/concerns.sql`. A change of a
# row gives a new digest. The digest is the first 12 hex digits of the git
# object name of their canonical JSON, the same on each host.
unit_frame() {
  local root=$1 concerns
  concerns=$(sqlite3 -json :memory: ".read $root/ledger/concerns.sql" 'SELECT id FROM concern ORDER BY id;')
  jq -n -S -c -L "$root/.config/claims" --argjson concerns "$concerns" \
    'include "sections"; {axes: axes, questions: questions, concerns: [$concerns[].id]}' \
    | git hash-object --stdin | awk '{ print substr($1, 1, 12) }'
}

# The marker that `unit:sign` writes on the issue: the frame's digest in an
# HTML comment, which the second landing of #7018 reads at a claim.
unit_frame_marker() {
  printf '<!-- signed frame=%s -->\n' "$1"
}
