#!/usr/bin/env bash
# Prints the `check:*` tasks a gate runs for the change in this worktree, one
# per line (#4911, `select.jq`). The change is every path the working tree
# changes against its fork from `origin/$trunk`, the trunk
# (`.config/pr-stack/trunk.bash`, #5443), committed or not, and every
# untracked path git does not ignore. With a commit as its argument, the
# change is every path that commit changes against its fork, as `passed.bash`
# reads a head (#5076). Without the trunk the change is unknown, and it
# selects every group. With `--landing`, the script prints only the checks
# the landing's gate runs (#5458): `mise run check` and `passed.bash require`
# read those.
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
