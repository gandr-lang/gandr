# shellcheck shell=bash
# The tools that a nested `mise run` of a case disables, sourced by each
# harness that runs a task with a tool disabled.
#
# `MISE_DISABLE_TOOLS` replaces the `disable_tools` setting of the host's
# configuration, and does not add to it. A case that sets the variable to its
# own tool alone enables each tool that the host disables, and the nested
# `mise` then installs that tool. So a case sets the variable to the list that
# `disabled_tools` prints.

# Prints the effective list of disabled tools, with each tool in `$@` added:
# the `disable_tools` setting without the variable, then the tools that
# `MISE_DISABLE_TOOLS` names, then `$@`. Each tool occurs once, in the order
# of its first occurrence, and a comma separates two tools.
disabled_tools() {
  local configured
  configured=$(env -u MISE_DISABLE_TOOLS mise settings get disable_tools 2> /dev/null | jq -r '.[]?' 2> /dev/null) || configured=''
  local -a tools=()
  local tool named=${MISE_DISABLE_TOOLS:-}
  while IFS= read -r tool; do
    [[ -n $tool ]] && tools+=("$tool")
  done <<< "$configured"$'\n'"${named//,/$'\n'}"
  tools+=("$@")
  local -A seen=()
  local -a unique=()
  for tool in "${tools[@]}"; do
    [[ -n ${seen[$tool]:-} ]] && continue
    seen[$tool]=1
    unique+=("$tool")
  done
  local IFS=,
  printf '%s\n' "${unique[*]}"
}
