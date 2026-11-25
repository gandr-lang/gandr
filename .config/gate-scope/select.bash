#!/usr/bin/env bash
# Prints the `check:*` tasks that a gate runs for the change in this worktree,
# one on each line. The change is each path that the working tree changes
# against its fork from the trunk, committed or not. It also holds each
# untracked path that git does not ignore.
# - see: #4911, #5443, `select.jq`, `.config/pr-stack/trunk.bash`
#
# With a commit as its argument, the change is each path that the commit
# changes against its fork. `gate pass require` reads a head the same way.
# Without the trunk the change is unknown, so the script selects each group.
# With `--landing`, the script prints only the checks of the landing's gate.
# `mise run check` and `gate pass require` read those.
# - see: #5076, #5458
#
# `GATE_TASKS`, when set, is the JSON list of every `check:*` task's name, and
# mise is not asked for it: a record of a passed gate carries the list for its
# tree (#5076).
#
# Usage: select.bash [--landing] [<commit>]
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
source "$here/../pr-stack/trunk.bash"
landing=false
if [[ ${1:-} == --landing ]]; then
  landing=true
  shift
fi
head=${1:-}
tasks=${GATE_TASKS:-$(mise tasks ls --json | jq -c '[.[] | .name | select(startswith("check:"))]')}
if ! base=$(git merge-base "origin/$trunk" "${head:-HEAD}" 2> /dev/null); then
  echo "check: no fork from origin/$trunk to read the change against; the change selects every group" >&2
  jq -n -r --argjson tasks "$tasks" --argjson landing "$landing" '{tasks: $tasks, changed: ["."], landing: $landing}' \
    | jq -r -L "$here" -f "$here/select.jq" \
    | jq -r '.[]'
  exit 0
fi
# The `.rs` paths whose change touches `//` comments alone (`comments.bash`,
# #6648) go to jq as a file, as the changed paths go on its standard input.
comments=$(mktemp)
trap 'rm -f "$comments"' EXIT
"$here/comments.bash" "$base" ${head:+"$head"} > "$comments"
# The changed paths reach jq on its standard input, never as an argument: a
# large change makes a list longer than one argument can hold (#5220).
{
  if [[ -n $head ]]; then
    git diff --no-renames --name-only "$base" "$head"
  else
    git diff --no-renames --name-only "$base"
    git ls-files --others --exclude-standard
  fi
} | jq -nR --argjson tasks "$tasks" --argjson landing "$landing" --rawfile comments "$comments" \
  '{tasks: $tasks, changed: [inputs], comments: ($comments | split("\n") | map(select(length > 0))), landing: $landing}' \
  | jq -r -L "$here" -f "$here/select.jq" \
  | jq -r '.[]'
