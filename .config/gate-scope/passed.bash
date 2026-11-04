#!/usr/bin/env bash
# The records of passed gates (#5076, `passed.jq`). `mise run check` and
# `mise run gate:all` record each pass: the tree they passed on, the commit
# under it, the checks they ran and every `check:*` task the tree holds.
# `pr:open` and `pr:land` read the records and refuse a head that no gate
# passed on.
#
# The records are under the repository's common git directory, so a gate in
# one worktree counts for the same tree in another. Each record is one file,
# written once under its tree's directory and never changed. A gate that
# fails, stops or crashes writes no record. The tree holds the task files, so
# the task list a record carries is the list for that tree, and a lookup does
# not ask mise for it.
#
# Usage:
#   passed.bash tree
#     Prints the tree of the work in this worktree: the index, the working
#     tree and every untracked path git does not ignore.
#   passed.bash record <gate> <tree> <check>...
#     Records that <gate> ran the checks on <tree> and passed. When the work
#     is no longer <tree>, it records nothing: the work changed while the
#     gate ran.
#   passed.bash require <command> <commit>
#     Exits 0 when a gate passed on the tree of <commit> and ran every check
#     that the commit's change selects (`select.bash`). Otherwise it names
#     the command to run, and exits 2.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
records=$(git rev-parse --path-format=absolute --git-common-dir)/gandr-gate

# A copy of the index keeps its file stamps, so `git add` reads only the
# changed files. The real index does not change.
work_tree() {
  local index
  index=$(mktemp)
  if ! cp "$(git rev-parse --path-format=absolute --git-path index)" "$index" 2> /dev/null; then rm -f "$index"; fi
  GIT_INDEX_FILE=$index git add -A :/
  GIT_INDEX_FILE=$index git write-tree
  rm -f "$index"
}

case ${1:-} in
  tree)
    work_tree
    ;;
  record)
    (( $# >= 3 )) || { echo 'usage: passed.bash record <gate> <tree> <check>...' >&2; exit 2; }
    gate=$2
    tree=$3
    shift 3
    if [[ $(work_tree) != "$tree" ]]; then
      echo "$gate: the work changed while the gate ran, so no pass is recorded; run \`mise run $gate\` again before \`pr:open\` or \`pr:land\`" >&2
      exit 0
    fi
    mkdir -p "$records/$tree"
    file=$(mktemp "$records/$tree/.record.XXXXXX")
    tasks=$(mise tasks ls --json | jq -c '[.[] | .name | select(startswith("check:"))]')
    jq -n --arg tree "$tree" --arg commit "$(git rev-parse HEAD)" --arg gate "$gate" --argjson tasks "$tasks" \
      '{tree: $tree, commit: $commit, gate: $gate, checks: $ARGS.positional, tasks: $tasks}' --args "$@" > "$file"
    mv "$file" "$records/$tree/${file##*/.record.}.json"
    echo "$gate: passed on the tree $tree; \`pr:open\` and \`pr:land\` accept a head with this tree"
    ;;
  require)
    (( $# == 3 )) || { echo 'usage: passed.bash require <command> <commit>' >&2; exit 2; }
    command=$2
    commit=$3
    tree=$(git rev-parse "$commit^{tree}")
    shopt -s nullglob
    files=("$records/$tree"/*.json)
    if (( ${#files[@]} == 0 )); then
      echo "$command: no gate passed on the tree of $commit; run \`mise run check\` on it, then \`$command\` again" >&2
      exit 2
    fi
    passed=$(jq -cs . "${files[@]}")
    selected=$(GATE_TASKS=$(jq -c '.[0].tasks' <<< "$passed") "$here/select.bash" "$commit" 2> /dev/null | jq -R . | jq -cs .)
    verdict=$(jq -n --arg tree "$tree" --argjson selected "$selected" --argjson records "$passed" \
      '{tree: $tree, selected: $selected, records: $records}' | jq -c -f "$here/passed.jq")
    if jq -e .accepted <<< "$verdict" > /dev/null; then exit 0; fi
    echo "$command: the gates that passed on the tree of $commit did not run $(jq -r '.missing | join(", ")' <<< "$verdict"), which its change selects; run \`mise run check\` on it, then \`$command\` again" >&2
    exit 2
    ;;
  *)
    echo 'usage: passed.bash (tree | record <gate> <tree> <check>... | require <command> <commit>)' >&2
    exit 2
    ;;
esac
