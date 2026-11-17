# The vault's pages by filename (#2793), sourced by `unit:check`, `pr:open`
# and `refs:list`. An issue names a vault page by its filename; the tree cites
# it by its `mint:`, the uuid a rename leaves alone. This reading is the one
# place the two meet.

# The vault checkout `$XDG_CONFIG_HOME/gandr/references` names (`vault
# <path>`), or nothing when none is configured or it does not exist.
vault_checkout() {
  local config=${XDG_CONFIG_HOME:-$HOME/.config}/gandr/references vault
  [[ -f $config ]] || return 0
  vault=$(awk '$1 == "vault" { sub(/^vault[[:space:]]+/, ""); print }' "$config")
  if [[ -n $vault && -d $vault ]]; then printf '%s\n' "$vault"; fi
}

# Every page of the vault by its filename, as one JSON object: each filename
# its pages' mints, `null` for a page that carries no `mint:` line. Prints
# `null` where no vault checkout is configured, so a reading without one is a
# reading for shape alone.
vault_pages() {
  local vault
  vault=$(vault_checkout)
  if [[ -z $vault ]]; then
    echo null
    return 0
  fi
  {
    git -C "$vault" ls-files -- '*.md' | awk '{ print "page\t" $0 }'
    git -C "$vault" grep -m1 -E '^mint: [0-9a-f-]{36}$' -- '*.md' \
      | awk '{ at = index($0, ":mint: "); print "mint\t" substr($0, 1, at - 1) "\t" substr($0, at + 7) }'
  } | jq -Rn '
      [inputs | split("\t")] as $rows
      | ([$rows[] | select(.[0] == "mint") | {key: .[1], value: .[2]}] | from_entries) as $mints
      | [$rows[] | select(.[0] == "page") | .[1] | {name: (split("/") | last), mint: $mints[.]}]
      | group_by(.name)
      | map({key: .[0].name, value: map(.mint)})
      | from_entries'
}

# The vault's programme and plan pages' absorption statuses by filename
# (#3161), as the vault's `report:absorption` writes them beside the
# references file: `{"<filename>": [{path, status}]}`. Prints `null` where
# the file has not been written, as in CI, so the pairing check
# (`absorbing.jq`) reads nothing to pair.
vault_absorption() {
  local file=${XDG_CONFIG_HOME:-$HOME/.config}/gandr/absorption.json
  if [[ -f $file ]]; then jq -c . "$file"; else echo null; fi
}
