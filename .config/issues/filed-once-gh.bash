#!/usr/bin/env bash
# The `gh` that `filed-once.bash` puts first on the path (#5149): one GitHub
# for every run of a case, kept in the directory `$STUB_GH`. The epic #4481
# holds `$STUB_SUBS` sub-issues. Above 99 it refuses a link as GitHub does,
# after the issue exists. The board of refactor issues is `board.json`, and
# each create adds its issue to it. `deps_issues`' query (#5709) is answered
# from the board and the epic. The first two board reads wait for each
# other, so two runs both read the board before either one creates. Every call
# is a line of `calls`.
set -euo pipefail
dir=${STUB_GH:?}
board=$dir/board.json
printf '%s\n' "$*" >> "$dir/calls"
# Hold the board while this call reads and writes it, with `host-lock.bash`'s
# lock: `flock(1)` where the host has it and perl's `flock` on macOS. The
# stub runs through a link, so its own directory is the link's target's.
source "$(dirname "$(readlink "${BASH_SOURCE[0]}" || echo "${BASH_SOURCE[0]}")")/../mise/host-lock.bash"
locked() {
  exec 7> "$dir/board.lock"
  until host_flock 7; do sleep 0.05; done
}
case "$*" in
  "auth token"*) exit 1 ;;
  "repo view"*) echo case/case ;;
  "api graphql"*)
    query=
    for arg in "$@"; do
      [[ $arg != query=* ]] || query=${arg#query=}
    done
    if [[ $query != *issueOrPullRequest* ]]; then
      cat "$dir/pr.json"
      exit 0
    fi
    # Each issue the query names: #4481 is an open epic whose page holds at
    # most 100 of its sub-issues, as GitHub's does. A number on no board is
    # null, as a pull request is.
    locked
    jq -c --arg query "$query" --argjson subs "${STUB_SUBS:?}" '
      def listed($total): {totalCount: $total, nodes: [range([$total, 100] | min) | {number: (. + 1), state: "OPEN"}]};
      . as $board
      | {data: {repository: ([$query | scan("i([0-9]+): issueOrPullRequest") | .[0] | tonumber]
        | map(. as $n | {key: "i\($n)", value: (
            if $n == 4481 then {number: $n, state: "OPEN", title: "epic", labels: {nodes: [{name: "kind:epic"}]}, subIssues: listed($subs)}
            else first($board[] | select(.number == $n) | {number: $n, state, title, labels: {nodes: []}, subIssues: listed(0)}) // null
            end
            | if . == null then null else . + {fullDatabaseId: "\($n)", parent: null, blockedBy: listed(0), blocking: listed(0)} end)})
        | from_entries)}}' "$board"
    ;;
  "issue list"*)
    locked
    reads=$(($(cat "$dir/reads" 2> /dev/null || echo 0) + 1))
    echo "$reads" > "$dir/reads"
    host_unlock 7
    if ((reads <= 2)); then
      for _ in $(seq 300); do
        (($(cat "$dir/reads") >= 2)) && break
        sleep 0.1
      done
    fi
    locked
    cat "$board"
    ;;
  "issue create"*)
    file= title=
    args=("$@")
    for ((i = 0; i < ${#args[@]}; i++)); do
      [[ ${args[i]} != --body-file ]] || file=${args[i + 1]}
      [[ ${args[i]} != --title ]] || title=${args[i + 1]}
    done
    locked
    number=$(($(jq length "$board") + 1))
    jq --argjson n "$number" --arg title "$title" --rawfile body "$file" '. + [{number: $n, state: "OPEN", title: $title, body: $body}]' "$board" > "$board.new"
    mv "$board.new" "$board"
    echo "https://github.com/case/case/issues/$number"
    ;;
  "issue close"*)
    locked
    jq --argjson n "$3" 'map(if .number == $n then .state = "CLOSED" else . end)' "$board" > "$board.new"
    mv "$board.new" "$board"
    ;;
  "api -X POST repos/{owner}/{repo}/issues/4481/sub_issues"*)
    if ((STUB_SUBS >= 100)); then
      echo 'gh: Parent cannot have more than 100 sub-issues (HTTP 422)' >&2
      exit 1
    fi
    echo '{}'
    ;;
  "api -X POST "*) echo '{}' ;;
  *)
    echo "filed-once-gh: no answer for: $*" >&2
    exit 1
    ;;
esac
