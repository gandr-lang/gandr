# The design work that no open issue holds (#3401), sourced by
# `report:design` and `claim:next`. `design.jq` holds the rule.

design_here=$(dirname "${BASH_SOURCE[0]}")
# shellcheck source=/dev/null
source "$design_here/../references/vault.bash"

# One line for each design page and each open unit of a vault unit table that
# no open issue in the file $1 names (`design.jq`); $1 holds the open issues
# as [{number, body}], or a list with more fields. Prints nothing where no
# vault checkout is configured, as in CI. A page is read when one of its
# table headers holds a `complete` cell, so the reading reads few files.
design_report() {
  local issues=$1 vault pages
  vault=$(vault_checkout)
  [[ -n $vault ]] || return 0
  pages=$(mktemp)
  { git -C "$vault" grep -l -I -i -E '^[[:space:]]*\|(.*\|)?[[:space:]]*complete[[:space:]]*\|' -- '*.md' || true; } \
    | while read -r path; do
        jq -n -c --arg name "${path##*/}" --rawfile text "$vault/$path" '{name: $name, text: $text}'
      done | jq -s -c . > "$pages"
  jq -n -c --argjson absorption "$(vault_absorption)" --slurpfile pages "$pages" --slurpfile issues "$issues" \
    '{absorption: $absorption, pages: $pages[0], issues: $issues[0]}' \
    | jq -r -L "$design_here" -L "$design_here/../issues" -f "$design_here/design.jq"
  rm -f "$pages"
}
