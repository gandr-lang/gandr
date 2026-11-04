#!/usr/bin/env bash
# Prints the `check:*` tasks `mise run check` runs for the change in this
# worktree, one per line (#4911, `select.jq`). The change is every path the
# working tree changes against its fork from `origin/main`, committed or not,
# and every untracked path git does not ignore. With a commit as its argument,
# the change is every path that commit changes against its fork, as
# `passed.bash` reads a head (#5076). Without `origin/main` the change is
# unknown, and every check is printed.
#
# `GATE_TASKS`, when set, is the JSON list of every `check:*` task's name, and
# mise is not asked for it: a record of a passed gate carries the list for its
# tree (#5076).
#
# Usage: select.bash [<commit>]
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
head=${1:-}
tasks=${GATE_TASKS:-$(mise tasks ls --json | jq -c '[.[] | .name | select(startswith("check:"))]')}
if ! base=$(git merge-base origin/main "${head:-HEAD}" 2> /dev/null); then
  echo "check: no fork from origin/main to read the change against; every check runs" >&2
  jq -r '.[]' <<< "$tasks"
  exit 0
fi
if [[ -n $head ]]; then
  changed=$(git diff --no-renames --name-only "$base" "$head" | jq -R . | jq -cs .)
else
  changed=$({ git diff --no-renames --name-only "$base"; git ls-files --others --exclude-standard; } | jq -R . | jq -cs .)
fi
jq -n --argjson tasks "$tasks" --argjson changed "$changed" '{tasks: $tasks, changed: $changed}' \
  | jq -r -L "$here" -f "$here/select.jq" \
  | jq -r '.[]'
