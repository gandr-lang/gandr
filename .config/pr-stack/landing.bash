#!/usr/bin/env bash
# The server-side landing watcher and CI depth gate (#2701, #5074).
# `.github/workflows/landing.yml` runs the watcher on each CI completion.
# `.github/workflows/ci.yml` runs `depth` before other pull request jobs.
# The watcher reads each open pull request once.
# `landing.jq` decides each action.
# `stack.bash` applies the stacking rule.
#
# A token that may queue lets the watcher queue a green stack.
# `LANDING_TOKEN_HELD` records that token.
# The watcher tells a seat when a stack needs a hand.
# The comment mark identifies the pull request head.
#
# The caller sets `GH_TOKEN`.
# The caller sets `LANDING_TOKEN_HELD` when a token may queue.
# The depth caller sets `CI_PULL_REQUEST` and `GITHUB_RUN_ID`.
# A failed action prints a warning.
# The next run reads the server again.
set -euo pipefail
repo=${GITHUB_REPOSITORY:-$(gh repo view --json nameWithOwner --jq .nameWithOwner)}
source "$(git rev-parse --show-toplevel)/.config/pr-stack/stack.bash"
token=${LANDING_TOKEN_HELD:-false}
required=$(required_contexts)
# The CI workflow, which `landing.yml` runs on and the depth gate cancels:
# the `name` of `.github/workflows/ci.yml`.
ci_workflow=CI

# The open pull requests, held ones left out (a draft, or the owner's
# `hold:owner`, #3253), as `landing.jq` reads them.
read_prs() {
  local pr number head base upstream rollup gated
  gh api graphql --paginate -f owner="${repo%/*}" -f name="${repo#*/}" -f query='
    query($owner: String!, $name: String!, $endCursor: String) {
      repository(owner: $owner, name: $name) {
        pullRequests(states: OPEN, first: 20, after: $endCursor) {
          pageInfo { hasNextPage endCursor }
          nodes {
            number isDraft headRefName headRefOid baseRefName createdAt isInMergeQueue mergeStateStatus
            autoMergeRequest { enabledAt }
            labels(first: 50) { nodes { name } }
            stack { number }
            author { __typename }
            commits(last: 1) { nodes { commit { statusCheckRollup { contexts(first: 100) { nodes {
              __typename
              ... on CheckRun { name status conclusion startedAt checkSuite { workflowRun { workflow { name } } } }
              ... on StatusContext { context state startedAt: createdAt } } } } } } }
            timelineItems(last: 1, itemTypes: [ADDED_TO_MERGE_QUEUE_EVENT, REMOVED_FROM_MERGE_QUEUE_EVENT, HEAD_REF_FORCE_PUSHED_EVENT, PULL_REQUEST_COMMIT]) { nodes { __typename ... on RemovedFromMergeQueueEvent { reason } } }
            comments(last: 100) { nodes { body } }
          }
        }
      }
    }' --jq '.data.repository.pullRequests.nodes[] | select((.isDraft or any(.labels.nodes[]; .name == "hold:owner")) | not)' \
    | while IFS= read -r pr; do
        number=$(jq -r .number <<< "$pr")
        head=$(jq -r .headRefOid <<< "$pr")
        # A dequeued head GitHub would rebase: the commits its base already
        # carries, which that rebase replays empty (#4463). The checkout holds
        # every branch as the run began; the fetch brings either up to date.
        upstream='[]'
        if [[ $(jq -r '.timelineItems.nodes[0].__typename' <<< "$pr") == RemovedFromMergeQueueEvent ]]; then
          base=$(jq -r .baseRefName <<< "$pr")
          git fetch --quiet origin "$base" "$head" 2> /dev/null || true
          if git cat-file -e "$head^{commit}" 2> /dev/null && git rev-parse --verify --quiet "origin/$base" > /dev/null; then
            upstream=$(upstream_replays "origin/$base" "$head" | jq -R . | jq -cs .)
          fi
        fi
        rollup=$(jq '.commits.nodes[0].commit.statusCheckRollup.contexts.nodes // []' <<< "$pr")
        # A pull request the depth gate stopped (#5074) carries its mark for
        # this head. Its cancelled checks wait for its promotion, so they read
        # as pending, never red. It waits while its CI run has not started
        # again (`unstarted.jq`, #5171).
        gated=$(jq '.headRefOid as $head | any(.comments.nodes[].body; contains("<!-- landing:pr-depth:\($head) -->"))' <<< "$pr")
        jq -c --argjson reading "$(jq -c --argjson required "$required" --argjson gated "$gated" -f "$pr_stack_dir/required.jq" <<< "$rollup")" \
          --argjson unstarted "$(jq -c --argjson required "$required" --arg workflow "$ci_workflow" -f "$pr_stack_dir/unstarted.jq" <<< "$rollup")" \
          --argjson upstream "$upstream" \
          '{number, oid: .headRefOid, head: .headRefName, base: .baseRefName,
            queued: (.isInMergeQueue or .autoMergeRequest != null),
            held: any(.labels.nodes[]; .name == "landing"),
            bot: (.author.__typename == "Bot"),
            stack: .stack.number,
            merge: .mergeStateStatus,
            reading: $reading,
            removed: (.timelineItems.nodes[0].__typename == "RemovedFromMergeQueueEvent"),
            removal: (.timelineItems.nodes[0].reason // "" | ascii_downcase),
            upstream: $upstream,
            marks: [.comments.nodes[].body | scan("<!-- landing:(pr-[a-z]+):([0-9a-f]{40}) -->") | "\(.[0]):\(.[1])"]}
          | .oid as $oid | . + {waiting: ($unstarted and (.marks | index("pr-depth:\($oid)")) != null)}' <<< "$pr"
      done | jq -cs . | jq -c --arg trunk "$trunk" -f "$pr_stack_dir/depths.jq"
}

# Comment the event line `$2` on pull request `$1`, marked for its head `$4`
# as event `$3`, with the explanation `$5`.
tell() {
  gh pr comment "$1" -R "$repo" --body "$(printf '%s\n\n%s\n\n<!-- landing:%s:%s -->' "$2" "$5" "$3" "$4")" > /dev/null \
    || echo "::warning::#$1: the $3 comment failed"
}

# The CI depth gate (#5074), run first in a pull request's CI run: above
# depth 3 the run is cancelled before any lane starts, so the runners go to
# the three members that land next and to the merge groups. The pull request
# is told once a head; the watcher's promotion runs the run again once a
# landing moves it to depth 3. A reading that fails runs the whole CI.
depth_gate() {
  local number=$1 head=$2 depth
  depth=$(stack_depth "$number") || return 0
  (( depth > 3 )) || return 0
  if ! depth_marked "$number" "$head"; then
    tell "$number" "pr-depth #$number waits at stack depth $depth" pr-depth "$head" \
      "Full CI runs for the bottom three pull requests of a stack only. This one is at depth $depth: its run stopped before any lane, and the landing watcher runs it again once a landing moves it to depth 3."
  fi
  gh api --method POST "repos/$repo/actions/runs/$GITHUB_RUN_ID/cancel" > /dev/null || return 0
  # The cancellation ends this job; nothing after it runs meanwhile.
  sleep 300
}

if [[ ${1:-} == depth ]]; then
  depth_gate "${CI_PULL_REQUEST:?}" "${CI_HEAD:?}"
  exit 0
fi

# The run's GraphQL spend, read before and after from the free `rate_limit`
# endpoint and printed last, so a costly run shows in its own log.
spent_before=$(command gh api rate_limit --jq .resources.graphql.used 2> /dev/null) || spent_before=
trap 'if [[ -n $spent_before ]] && spent_after=$(command gh api rate_limit --jq .resources.graphql.used 2> /dev/null); then echo "landing: $((spent_after - spent_before)) GraphQL points this run"; fi' EXIT
prs=$(read_prs)
actions=$(jq -c --argjson token "$token" '{token: $token, prs: .}' <<< "$prs" | jq -c -f "$pr_stack_dir/landing.jq")
err=$(mktemp)
while IFS= read -r action; do
  number=$(jq -r .number <<< "$action")
  act=$(jq -r .act <<< "$action")
  oid=$(jq -r --argjson n "$number" '.[] | select(.number == $n) | .oid' <<< "$prs")
  status=0
  case "$act" in
    land)
      echo "#$number: landing its stack's ready prefix"
      land_prefix "$number" || status=$?
      # 3: the stack waits on a queued unit or pull request; the next run reads it again.
      if (( status != 0 && status != 3 )); then echo "::warning::#$number: the landing failed ($status)"; fi
      ;;
    restack)
      # A member queued since the reading is never moved, nor one above it (#2531).
      if [[ $(queued_of "$(server_stack "$number")") != '[]' ]]; then
        echo "#$number: a member of its stack is queued now; nothing is pushed"
      elif moved=$(signed_restack "$(jq -r --argjson n "$number" '.[] | select(.number == $n) | .head' <<< "$prs")" "$oid" \
        "$(jq -r --argjson n "$number" '.[] | select(.number == $n) | .base' <<< "$prs")" 2> "$err"); then
        if [[ -n $moved ]]; then
          echo "#$number: the watcher restacks it onto its base as signed commits"
          tell "$number" "pr-restacked #$number" pr-restacked "$oid" \
            "The merge queue removed this pull request with no red check in its stack. The landing watcher replayed its commits onto its base as commits GitHub signs. It lands once its checks are green."
        else
          # The head already stands on its base: what made the queue remove
          # it was ahead of it in the queue, so it queues again unchanged.
          echo "#$number: it already stands on its base; landing its stack's ready prefix again"
          tell "$number" "pr-restacked #$number" pr-restacked "$oid" \
            "The merge queue removed this pull request with no red check in its stack, and it already stands on its base. The landing watcher queues it again."
          land_prefix "$number" || status=$?
          if (( status != 0 && status != 3 )); then echo "::warning::#$number: the landing failed ($status)"; fi
        fi
      elif [[ $(jq -r .told <<< "$action") != true ]]; then
        echo "#$number: the restack failed: $(< "$err")"
        tell "$number" "pr-dequeued #$number" pr-dequeued "$oid" \
          "The merge queue removed this pull request, and the landing watcher could not restack it onto its base: $(< "$err"). Rebase it, then \`pr:land $number\`."
      fi
      ;;
    green)
      tell "$number" "pr-green #$number" pr-green "$oid" \
        "Every required check passed on this head and the pull request is out of the merge queue: \`pr:land $number\` queues its stack's ready prefix."
      ;;
    dequeued)
      if [[ $(jq -r '.upstream // [] | length' <<< "$action") != 0 ]]; then
        tell "$number" "pr-dequeued #$number" pr-dequeued "$oid" \
          "The merge queue removed this pull request, and its branch holds commits whose change its base already carries: $(jq -r '.upstream | map("`\(.)`") | join(", ")' <<< "$action"). \`pr:land $number\` restacks it onto \`$trunk\` and drops them."
      else
        tell "$number" "pr-dequeued #$number" pr-dequeued "$oid" \
          "The merge queue removed this pull request at this head. Read the entry's run, then \`pr:land $number\`, which restacks it onto \`$trunk\`."
      fi
      ;;
    red)
      tell "$number" "pr-red #$number $(jq -r '.failed | join(", ")' <<< "$action")" pr-red "$oid" \
        "A required check failed on this head; read its log, fix it, then \`pr:land $number\`."
      ;;
    dirty)
      tell "$number" "pr-dirty #$number" pr-dirty "$oid" \
        "This pull request conflicts with its base: rebase it, then \`pr:land $number\`."
      ;;
  esac
done < <(jq -c '.[]' <<< "$actions")

# The depth gate's promotion (#5074): a pull request the gate stopped that a
# landing has moved to depth 3 or less runs its cancelled CI run again, and
# the gate passes it this time. One run listing and one rerun request each.
# The rerun goes through `RERUN_TOKEN`, the workflow's own token: the job
# grants it `actions: write`, and the fine-grained `LANDING_TOKEN` holds no
# Actions permission, so GitHub refuses it the rerun (HTTP 403).
while read -r number oid; do
  run=$(gh api "repos/$repo/actions/workflows/ci.yml/runs?event=pull_request&head_sha=$oid&per_page=1" \
    --jq '.workflow_runs[0] | select(.conclusion == "cancelled") | .id') || continue
  [[ -n $run ]] || continue
  if GH_TOKEN=${RERUN_TOKEN:-$GH_TOKEN} gh api --method POST "repos/$repo/actions/runs/$run/rerun" > /dev/null 2> "$err"; then
    echo "#$number: at depth 3 or less; CI run $run runs again"
  else
    echo "::warning::#$number: the rerun of CI run $run failed: $(< "$err")"
  fi
done < <(jq -r '.[] | select(.waiting and .depth <= 3) | "\(.number) \(.oid)"' <<< "$prs")
