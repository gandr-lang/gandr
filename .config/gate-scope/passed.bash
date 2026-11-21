#!/usr/bin/env bash
# The records of passed gates (#5076, `passed.jq`). `mise run check` and
# `mise run gate:all` record each pass: the tree they passed on, the commit
# under it, the checks they ran, every `check:*` task the tree holds and the
# time the gate took (#5215). `pr:open` and `pr:land` read the records, and
# they run `mise run check` on a head that no gate passed on (#5458).
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
#   passed.bash record <gate> <tree> <log> <seconds> <wait> <check>...
#     Records that <gate> ran the checks on <tree> and passed in <seconds>,
#     with the times its log <log> holds (`times.jq`, #5215) and its wait
#     <wait> for its lane's lock and its slot, `{"lane": <s>, "slot": <s>}`
#     (`gate_wait`, #6699). When the work is no longer <tree>, it records
#     nothing: the work changed while the gate ran. A log that gives no times
#     leaves the record's `time` null, and the pass is recorded all the same.
#   passed.bash require <command> <commit>
#     Exits 0 when a gate passed on the tree of <commit> and ran the cheap
#     set of `landing`, `check:landing` (#5458, #8224). Otherwise it names
#     the command to run, and exits 2.
#   passed.bash admit <host> <commit>
#     Records here the pass of a gate that ran on <host> (`gate:remote`,
#     #6996). Standard input holds the far records of the tree of <commit>.
#     The newest record of <commit> on that tree, carried from no other
#     tree, is written here with `host` added. So the record names the head,
#     the host and each check, and `require` reads it as a local one. Exits
#     2, naming why, when standard input holds no such record.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
records=$(git rev-parse --path-format=absolute --git-common-dir)/gandr-gate

# A copy of the index keeps its file stamps, so `git add` reads only the
# changed files. The real index does not change. The copy also keeps the
# index's own stamp. Git reads an entry again by content when the entry is
# not older than the index. A copy stamped now hides that.
work_tree() {
  local index
  index=$(mktemp)
  if ! cp -p "$(git rev-parse --path-format=absolute --git-path index)" "$index" 2> /dev/null; then rm -f "$index"; fi
  GIT_INDEX_FILE=$index git add -A :/
  GIT_INDEX_FILE=$index git write-tree
  rm -f "$index"
}

case ${1:-} in
  tree)
    work_tree
    ;;
  record)
    (( $# >= 6 )) || { echo 'usage: passed.bash record <gate> <tree> <log> <seconds> <wait> <check>...' >&2; exit 2; }
    gate=$2
    tree=$3
    log=$4
    seconds=$5
    wait=$6
    shift 6
    if [[ $(work_tree) != "$tree" ]]; then
      echo "$gate: the work changed while the gate ran, so no pass is recorded; run \`mise run $gate\` again before \`pr:open\` or \`pr:land\`" >&2
      exit 0
    fi
    time=$(jq -n --rawfile log "$log" --argjson seconds "$seconds" --argjson wait "$wait" '{log: $log, seconds: $seconds, wait: $wait}' 2> /dev/null | jq -c -f "$here/times.jq" 2> /dev/null) || time=
    [[ -n $time ]] || { echo "$gate: the log $log gave no times, so the record holds none" >&2; time=null; }
    mkdir -p "$records/$tree"
    file=$(mktemp "$records/$tree/.record.XXXXXX")
    tasks=$(mise tasks ls --json | jq -c '[.[] | .name | select(startswith("check:"))]')
    jq -n --arg tree "$tree" --arg commit "$(git rev-parse HEAD)" --arg gate "$gate" --argjson tasks "$tasks" --argjson time "$time" \
      '{tree: $tree, commit: $commit, gate: $gate, checks: $ARGS.positional, tasks: $tasks, at: (now | todate), time: $time}' --args "$@" > "$file"
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
    selected='["check:landing"]'
    verdict=$(jq -n --arg tree "$tree" --slurpfile selected <(printf '%s\n' "$selected") --slurpfile records <(printf '%s\n' "$passed") \
      '{tree: $tree, selected: $selected[0], records: $records[0]}' | jq -c -f "$here/passed.jq")
    if jq -e .accepted <<< "$verdict" > /dev/null; then exit 0; fi
    echo "$command: the gates that passed on the tree of $commit did not run $(jq -r '.missing | join(", ")' <<< "$verdict"); run \`mise run check\` on it, then \`$command\` again" >&2
    exit 2
    ;;
  admit)
    (( $# == 3 )) || { echo 'usage: passed.bash admit <host> <commit>' >&2; exit 2; }
    host=$2
    commit=$(git rev-parse "$3^{commit}")
    tree=$(git rev-parse "$commit^{tree}")
    record=$(jq -sc --arg tree "$tree" --arg commit "$commit" --arg host "$host" \
      '[.[] | select(.tree == $tree and .commit == $commit and .carried == null)] | sort_by(.at) | last | select(. != null) | . + {host: $host}' 2> /dev/null) || record=
    if [[ -z $record ]]; then
      echo "gate:remote: $host gave no pass of $commit on its tree $tree, so none is recorded" >&2
      exit 2
    fi
    mkdir -p "$records/$tree"
    file=$(mktemp "$records/$tree/.record.XXXXXX")
    printf '%s\n' "$record" > "$file"
    mv "$file" "$records/$tree/${file##*/.record.}.json"
    echo "gate:remote: the gate on $host passed on the tree $tree; \`pr:open\` and \`pr:land\` accept a head with this tree"
    ;;
  *)
    echo 'usage: passed.bash (tree | record <gate> <tree> <log> <seconds> <check>... | require <command> <commit> | admit <host> <commit>)' >&2
    exit 2
    ;;
esac
