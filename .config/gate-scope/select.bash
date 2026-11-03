#!/usr/bin/env bash
# Prints the `check:*` tasks `mise run check` runs for the change in this
# worktree, one per line (#4911, `select.jq`). The change is every path the
# working tree changes against its fork from `origin/main`, committed or not,
# and every untracked path git does not ignore. Without `origin/main` the
# change is unknown, and every check is printed.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
tasks=$(mise tasks ls --json | jq -c '[.[] | .name | select(startswith("check:"))]')
if base=$(git merge-base origin/main HEAD 2> /dev/null); then
  changed=$({ git diff --no-renames --name-only "$base"; git ls-files --others --exclude-standard; } | jq -R . | jq -cs .)
else
  echo "check: no fork from origin/main to read the change against; every check runs" >&2
  jq -r '.[]' <<< "$tasks"
  exit 0
fi
jq -n --argjson tasks "$tasks" --argjson changed "$changed" '{tasks: $tasks, changed: $changed}' \
  | jq -r -L "$here" -f "$here/select.jq" \
  | jq -r '.[]'
