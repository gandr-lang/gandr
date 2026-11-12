# shellcheck shell=bash
# The lane table is factory state: the lanes that run, and the areas of each.
# It changes with each session of the factory, so it lives in the factory's
# directory and never in this tree. A change of the lanes needs no landing.
#
# The table is `lanes.toml` under `$XDG_CONFIG_HOME/gandr`: one `[lane]`
# table, each key a lane and each value the list of its areas. `GANDR_LANES`
# names another file; a check gives its fixture that way.
#
# Source this file. A host with no table, such as a hosted runner, reads no
# lane: `lanes_keys` prints `[]`, and a task that needs a row refuses.

# lanes_file: the path of the lane table.
lanes_file() {
  printf '%s\n' "${GANDR_LANES:-${XDG_CONFIG_HOME:-$HOME/.config}/gandr/lanes.toml}"
}

# lanes_list: the lanes of the table, one on each line, none with no table.
# The gate reads it with no jq (`.config/mise/gate.bash`).
lanes_list() {
  local file
  file=$(lanes_file)
  [[ -r $file ]] || return 0
  awk '/^\[lane\]/ { on = 1; next } /^\[/ { on = 0 } on && /^[a-z0-9-]+ *=/ { sub(/ *=.*/, ""); print }' "$file"
}

# lanes_keys: the lanes of the table as one JSON array, `[]` with no table.
lanes_keys() {
  lanes_list | jq -Rnc '[inputs]'
}

# lanes_has <lane>: whether the table holds a row for the lane.
lanes_has() {
  lanes_keys | jq -e --arg lane "$1" 'index($lane) != null' > /dev/null
}
