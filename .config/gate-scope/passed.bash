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
#   passed.bash record <gate> <tree> <log> <seconds> <check>...
#     Records that <gate> ran the checks on <tree> and passed in <seconds>,
#     with the times its log <log> holds (`times.jq`, #5215). When the work
#     is no longer <tree>, it records nothing: the work changed while the
#     gate ran. A log that gives no times leaves the record's `time` null,
#     and the pass is recorded all the same.
#   passed.bash require <command> <commit>
#     Exits 0 when a gate passed on the tree of <commit> and ran every check
#     of the landing's gate that the commit's change selects
#     (`select.bash --landing`, #5458). Otherwise it names the command to
#     run, and exits 2.
#   passed.bash carry <gated> <head> <base>
#     Carries the gate on the tree of <gated> to the tree of <head>, when
#     <head>'s own commits above <base> keep the patches of as many commits
#     at the tip of <gated> (`git patch-id --stable`). `pr:open` stacks a
#     branch on the top and rebases its own commits; the gate on those
#     commits counts on the rebased head, and the merge queue checks the
#     combination. The stack stays first come, first served: no seat gates
#     again for another's `pr:open`. Each carried record names the tree it
#     came from. Exits 0 when the trees are one, or once it carries; exits 2,
#     naming why, when <gated> has no record or a patch differs. Then
#     `pr:open` runs the gate on the new head.
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
    (( $# >= 5 )) || { echo 'usage: passed.bash record <gate> <tree> <log> <seconds> <check>...' >&2; exit 2; }
    gate=$2
    tree=$3
    log=$4
    seconds=$5
    shift 5
    if [[ $(work_tree) != "$tree" ]]; then
      echo "$gate: the work changed while the gate ran, so no pass is recorded; run \`mise run $gate\` again before \`pr:open\` or \`pr:land\`" >&2
      exit 0
    fi
    time=$(jq -n --rawfile log "$log" --argjson seconds "$seconds" '{log: $log, seconds: $seconds}' 2> /dev/null | jq -c -f "$here/times.jq" 2> /dev/null) || time=
    [[ -n $time ]] || { echo "$gate: the log $log gave no times, so the record holds none" >&2; time=null; }
    mkdir -p "$records/$tree"
    file=$(mktemp "$records/$tree/.record.XXXXXX")
    tasks=$(mise tasks ls --json | jq -c '[.[] | .name | select(startswith("check:"))]')
    jq -n --arg tree "$tree" --arg commit "$(git rev-parse HEAD)" --arg gate "$gate" --argjson tasks "$tasks" --argjson time "$time" \
      '{tree: $tree, commit: $commit, gate: $gate, checks: $ARGS.positional, tasks: $tasks, at: (now | todate), time: $time}' --args "$@" > "$file"
    mv "$file" "$records/$tree/${file##*/.record.}.json"
    echo "$gate: passed on the tree $tree; \`pr:open\` and \`pr:land\` accept a head with this tree"
    ;;
  carry)
    (( $# == 4 )) || { echo 'usage: passed.bash carry <gated> <head> <base>' >&2; exit 2; }
    gated=$(git rev-parse "$2^{commit}")
    head=$(git rev-parse "$3^{commit}")
    from=$(git rev-parse "$gated^{tree}")
    tree=$(git rev-parse "$head^{tree}")
    [[ $from != "$tree" ]] || exit 0
    shopt -s nullglob
    files=("$records/$from"/*.json)
    (( ${#files[@]} > 0 )) || { echo "pr:open: no gate passed on the tree of $gated, so none carries to $head" >&2; exit 2; }
    "$0" require pr:open "$gated" || exit 2
    count=$(git rev-list --count "$4..$head")
    patches() { git rev-list --reverse -n "$count" "$1" | while IFS= read -r c; do git show --format= "$c" | git patch-id --stable | awk '{ print $1 }'; done; }
    if (( count == 0 )) || [[ $(patches "$gated") != "$(patches "$head")" ]]; then
      echo "pr:open: the stacked head's $count own commits do not keep the patches the gate on $gated passed" >&2
      exit 2
    fi
    mkdir -p "$records/$tree"
    for f in "${files[@]}"; do
      file=$(mktemp "$records/$tree/.record.XXXXXX")
      jq --arg tree "$tree" --arg commit "$head" --arg from "$from" '. + {tree: $tree, commit: $commit, carried: $from}' "$f" > "$file"
      mv "$file" "$records/$tree/${file##*/.record.}.json"
    done
    echo "pr:open: the gate on the tree $from carries to the stacked tree $tree: its $count own commits keep their patches"
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
    # A carried record (`carry`) took its gate from a head this reading
    # accepted, with that head's selection. The stacked head's change against
    # the trunk adds the commits of the pull requests below it, which their
    # own gates and the merge queue check, so its selection is not read again.
    if jq -e 'any(.[]; .carried != null)' <<< "$passed" > /dev/null; then exit 0; fi
    selected=$(GATE_TASKS=$(jq -c '.[0].tasks' <<< "$passed") "$here/select.bash" --landing "$commit" 2> /dev/null | jq -R . | jq -cs .)
    verdict=$(jq -n --arg tree "$tree" --argjson selected "$selected" --argjson records "$passed" \
      '{tree: $tree, selected: $selected, records: $records}' | jq -c -f "$here/passed.jq")
    if jq -e .accepted <<< "$verdict" > /dev/null; then exit 0; fi
    echo "$command: the gates that passed on the tree of $commit did not run $(jq -r '.missing | join(", ")' <<< "$verdict"), which its change selects; run \`mise run check\` on it, then \`$command\` again" >&2
    exit 2
    ;;
  *)
    echo 'usage: passed.bash (tree | record <gate> <tree> <log> <seconds> <check>... | require <command> <commit> | carry <gated> <head> <base>)' >&2
    exit 2
    ;;
esac
