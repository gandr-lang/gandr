# The design pages that a unit's identifiers give its `## Sources` (#7019,
# `identifiers.jq`), sourced by `unit:check` after
# `.config/references/vault.bash`.
#
# `identifiers_check <body> <number> <parent> <before>` prints the lines of
# `identifiers.jq`. `<parent>` is the number of the issue's parent on
# GitHub, or null, and `<before>` is JSON, a string or null, as
# `claim_before` prints it. The function reads the vault checkout that the
# references file names: its design pages are the pages under
# `docs/programme/` and `plans/`. One `git grep` finds the pages that name
# a mark of the unit's identifiers, and one jq run reads their text. A host
# with no vault prints one `note:` and refuses nothing.

identifiers_check() {
  local claims=${BASH_SOURCE[0]%/*} root vault rows crates design mark manifest
  local -a marks=() args=() found=()
  root=$(cd "$claims/../.." && pwd)
  vault=$(vault_checkout)
  if [[ -z $vault ]]; then
    echo "note: no vault checkout is configured, so unit:check reads no design page for the unit's identifiers"
    return 0
  fi
  # Each list is one name a line, which jq splits: a run of jq costs about
  # 10 ms, so the function runs three. `ledger/features.sql` is a dump, one
  # `INSERT` a row with its id first, so awk reads the ids without sqlite.
  rows=$(awk -F"'" '/^INSERT INTO feature VALUES\(/ { print $2 }' "$root/ledger/features.sql")
  for manifest in "$root"/crates/*/Cargo.toml; do
    manifest=${manifest%/Cargo.toml}
    crates+=${manifest##*/}$'\n'
  done
  design=$(git -C "$vault" -c core.quotePath=false ls-files -- 'docs/programme/*.md' 'plans/*.md')
  # The body and the lists have no bound on their size, so jq reads them
  # from files, and only the numbers go on its command line.
  mapfile -t marks < <(jq -n -r -L "$claims" --rawfile body <(printf '%s' "$1") --argjson number "$2" --argjson parent "$3" \
    --rawfile rows <(printf '%s' "$rows") --rawfile crates <(printf '%s' "$crates") \
    'include "sections"; $body | unit_identifiers($number; $parent; $rows | split("\n"); $crates | split("\n")) | identifier_marks[] | .grep')
  if (( ${#marks[@]} > 0 )); then
    for mark in "${marks[@]}"; do args+=(-e "$mark"); done
    # `git grep` exits 1 when no page names a mark.
    mapfile -t found < <(git -C "$vault" -c core.quotePath=false grep -l -E "${args[@]}" -- 'docs/programme/*.md' 'plans/*.md' || :)
  fi
  # The text of each page found, by its path. With no page found, jq reads
  # `/dev/null`, which gives no line.
  (cd "$vault" && jq -R -n -c --rawfile body <(printf '%s' "$1") --argjson number "$2" --argjson parent "$3" \
    --rawfile rows <(printf '%s' "$rows") --rawfile crates <(printf '%s' "$crates") \
    --rawfile design <(printf '%s' "$design") --slurpfile before <(printf '%s' "$4") \
    '(reduce inputs as $line ({}; .[input_filename] += $line + "\n")) as $texts
    | {number: $number, parent: $parent, body: $body, rows: ($rows | split("\n")), crates: ($crates | split("\n")),
       design: ($design | split("\n")), texts: $texts, before: $before[0]}' "${found[@]:-/dev/null}") \
    | jq -r -L "$claims" -f "$claims/identifiers.jq"
}
