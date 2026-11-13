#!/usr/bin/env bash
# The server-side landing watcher and CI depth gate (#2701, #5074).
# `.github/workflows/landing-queue.yml` runs the watcher on each CI completion.
# `.github/workflows/landing-checks.yml` runs `depth` before other pull request jobs.
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
source "$(git rev-parse --show-toplevel)/.config/gh/repo.bash"
repo=$(repo_name)
source "$(git rev-parse --show-toplevel)/.config/pr-stack/stack.bash"
# shellcheck source=sweep.bash
source "$pr_stack_dir/sweep.bash"
# shellcheck source=landed-heads.bash
source "$pr_stack_dir/landed-heads.bash"
token=${LANDING_TOKEN_HELD:-false}
# The landing-checks workflow, which `landing-queue.yml` runs on and the depth gate cancels:
# the `name` of `.github/workflows/landing-checks.yml`.
ci_workflow=landing-checks

# The open pull requests, held ones left out (a draft, or the owner's
# `hold:owner`, #3253), as `landing.jq` reads them. The head and base of
# every open pull request, held ones too, go to the file `$used_refs`, one a
# line: the landed heads the watcher deletes are never one of them (#6185).
# The first 100 changed files of each say whether it is a workflow change
# (#6915), and a pull request with more is read as one.
read_prs() {
  local pr number head base upstream rollup gated
  gh api graphql --paginate -F owner='{owner}' -F name='{repo}' -f query='
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
            commits(last: 1) { nodes { commit { committedDate statusCheckRollup { contexts(first: 100) { nodes {
              __typename
              ... on CheckRun { name status conclusion startedAt checkSuite { workflowRun { databaseId workflow { name } } } }
              ... on StatusContext { context state startedAt: createdAt } } } } } } }
            timelineItems(last: 1, itemTypes: [ADDED_TO_MERGE_QUEUE_EVENT, REMOVED_FROM_MERGE_QUEUE_EVENT, HEAD_REF_FORCE_PUSHED_EVENT, PULL_REQUEST_COMMIT]) { nodes { __typename ... on RemovedFromMergeQueueEvent { reason } } }
            bases: timelineItems(last: 1, itemTypes: [AUTOMATIC_BASE_CHANGE_FAILED_EVENT, AUTOMATIC_BASE_CHANGE_SUCCEEDED_EVENT, BASE_REF_CHANGED_EVENT]) { nodes { __typename ... on AutomaticBaseChangeFailedEvent { oldBase } } }
            comments(last: 100) { nodes { body } }
            files(first: 100) { pageInfo { hasNextPage } nodes { path } }
          }
        }
      }
    }' --jq '.data.repository.pullRequests.nodes[]' \
    | while IFS= read -r pr; do
        jq -r '.headRefName, .baseRefName' <<< "$pr" >> "${used_refs:-/dev/null}"
        if jq -e '.isDraft or any(.labels.nodes[]; .name == "hold:owner")' <<< "$pr" > /dev/null; then continue; fi
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
        # A head with no context of the `CI` workflow has no `CI` run
        # (#6164): GitHub starts none for a push while the pull request
        # conflicts, nor for a base edit. A head pushed in the last 5 minutes
        # may only wait for its run to register, so it is not read as unrun.
        ran=$(jq --arg workflow "$ci_workflow" 'any(.[]; .checkSuite.workflowRun.workflow.name? == $workflow)' <<< "$rollup")
        jq -c --argjson reading "$(jq -c --argjson required "$required" --argjson gated "$gated" -f "$pr_stack_dir/required.jq" <<< "$rollup")" \
          --argjson unstarted "$(jq -c --argjson required "$required" --arg workflow "$ci_workflow" -f "$pr_stack_dir/unstarted.jq" <<< "$rollup")" \
          --argjson upstream "$upstream" \
          --argjson ran "$ran" \
          '{number, oid: .headRefOid, head: .headRefName, base: .baseRefName,
            queued: (.isInMergeQueue or .autoMergeRequest != null),
            held: any(.labels.nodes[]; .name == "landing"),
            bot: (.author.__typename == "Bot"),
            stack: .stack.number,
            merge: .mergeStateStatus,
            reading: $reading,
            removed: (.timelineItems.nodes[0].__typename == "RemovedFromMergeQueueEvent"),
            removal: (.timelineItems.nodes[0].reason // "" | ascii_downcase),
            stranded: ((.bases.nodes[0] // {}) as $event | $event.__typename == "AutomaticBaseChangeFailedEvent" and $event.oldBase == .baseRefName),
            upstream: $upstream,
            marks: [.comments.nodes[].body | scan("<!-- landing:(pr-[a-z]+):([0-9a-f]{40}) -->") | "\(.[0]):\(.[1])"],
            unrun: (($ran | not) and (now - (.commits.nodes[0].commit.committedDate // "1970-01-01T00:00:00Z" | fromdate)) > 300),
            workflow: ((.files.pageInfo.hasNextPage // false) or any(.files.nodes[]?; .path | startswith(".github/workflows/")))}
          | .oid as $oid | . + {waiting: ($unstarted and (.marks | index("pr-depth:\($oid)")) != null)}' <<< "$pr"
      done | jq -cs . | jq -c --arg trunk "$trunk" -f "$pr_stack_dir/depths.jq"
}

# Comment the event line `$2` on pull request `$1`, marked for its head `$4`
# as event `$3`, with the explanation `$5`.
tell() {
  gh pr comment "$1" -R "$repo" --body "$(printf '%s\n\n%s\n\n<!-- landing:%s:%s -->' "$2" "$5" "$3" "$4")" > /dev/null \
    || echo "::warning::#$1: the $3 comment failed"
}

# Land pull request `$1`'s stack (`land_prefix`, #5695). Every line it writes
# goes to the run's log, and its last line is printed: what it queued, or why
# it refused. Its status is returned, and a 3 returns 0: the stack waits on a
# queued unit or pull request, and the next run reads it again.
landed() {
  local status=0 log
  log=$(mktemp)
  land_prefix "$1" 2> "$log" 1>&2 || status=$?
  cat "$log" >&2
  awk 'NF { line = $0 } END { print line }' "$log"
  rm -f "$log"
  (( status == 0 || status == 3 )) || return "$status"
}

# Tell the seat of pull request `$1`, at head `$2`, that the watcher could not
# queue its stack for the reason `$4` (#5695). The comment is `pr-dequeued`,
# and its event line carries the reason, so the page that `stall:watch` sends
# for the event names it. It is posted once a head: `$3` is true when the
# head already carries the mark. The run's log keeps a warning each time.
refused() {
  echo "::warning::#$1: the landing failed: $4"
  [[ $3 != true ]] || return 0
  tell "$1" "pr-dequeued #$1: $4" pr-dequeued "$2" \
    "The landing watcher could not queue the stack of this pull request. Do what the line above names, then \`pr:land $1\`."
}

# Do the action `$1` that `landing.jq` decided, from the reading `$prs`.
act_on() {
  local action=$1 number act oid told line moved
  number=$(jq -r .number <<< "$action")
  act=$(jq -r .act <<< "$action")
  told=$(jq -r '.told // false' <<< "$action")
  oid=$(jq -r --argjson n "$number" '.[] | select(.number == $n) | .oid' <<< "$prs")
  case "$act" in
    land)
      echo "#$number: landing its stack's ready prefix"
      line=$(landed "$number") || refused "$number" "$oid" "$told" "$line"
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
          # it was ahead of it in the queue, so it lands again unchanged. The
          # comment follows the landing, and says what it did (#5695).
          echo "#$number: it already stands on its base; landing its stack's ready prefix again"
          if line=$(landed "$number"); then
            tell "$number" "pr-restacked #$number" pr-restacked "$oid" \
              "The merge queue removed this pull request with no red check in its stack, and it already stands on its base. The landing watcher ran its landing again${line:+: $line}."
          else
            refused "$number" "$oid" "$told" "$line"
          fi
        fi
      elif [[ $told != true ]]; then
        echo "#$number: the restack failed: $(< "$err")"
        tell "$number" "pr-dequeued #$number" pr-dequeued "$oid" \
          "The merge queue removed this pull request, and the landing watcher could not restack it onto its base: $(< "$err"). Rebase it, then \`pr:land $number\`."
      fi
      ;;
    retarget)
      # GitHub could not change the base when the base's pull request merged
      # (#5776). So the pull request stays on a branch that is gone, in the
      # queue or out of it, and no landing reaches the trunk from it.
      # `retarget_bottom` takes it out of the queue, unstacks it and
      # retargets it to the trunk. The next run restacks or lands it.
      if retarget_bottom "$(jq -c --argjson n "$number" '.[] | select(.number == $n) | {number, base, stack, landing: .queued}' <<< "$prs")" \
        "$(server_stack "$number")" 2> "$err"; then
        cat "$err"
      else
        line=$(awk 'NF { line = $0 } END { print line }' "$err")
        echo "::warning::#$number: the retarget failed: $line"
        if [[ $told != true ]]; then
          tell "$number" "pr-dequeued #$number: $line" pr-dequeued "$oid" \
            "GitHub could not change the base of this pull request when its base merged, and the landing watcher could not retarget it to \`$trunk\`. Retarget it to \`$trunk\`, then \`pr:land $number\`."
        fi
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
    rerun)
      # GitHub started no `CI` run on this head (#6164), and `reopened`
      # starts one. The token that may queue is not the workflow's own,
      # whose events start no run. A pull request left closed is cut by the
      # stack watcher, so a failed reopen is tried once more.
      if gh pr close "$number" -R "$repo" > /dev/null 2> "$err"; then
        if gh pr reopen "$number" -R "$repo" > /dev/null 2> "$err" || gh pr reopen "$number" -R "$repo" > /dev/null 2> "$err"; then
          echo "#$number: its head has no CI run; closed and reopened, so CI runs"
          tell "$number" "pr-rerun #$number" pr-rerun "$oid" \
            "GitHub started no CI run on this head: a push while the pull request conflicts with its base starts none, and a base edit starts none. The landing watcher closed and reopened it, which starts CI. It lands once its checks are green."
        else
          echo "::warning::#$number: the reopen failed: $(< "$err")"
          tell "$number" "pr-unrun #$number" pr-unrun "$oid" \
            "GitHub started no CI run on this head. The landing watcher closed this pull request to start CI and could not reopen it: $(< "$err"). Reopen it, then \`pr:land $number\`."
        fi
      else
        echo "::warning::#$number: the close failed: $(< "$err")"
        tell "$number" "pr-unrun #$number" pr-unrun "$oid" \
          "GitHub started no CI run on this head, and the landing watcher could not close and reopen it: $(< "$err"). Close and reopen it, or push the branch again, then \`pr:land $number\`."
      fi
      ;;
    unrun)
      tell "$number" "pr-unrun #$number" pr-unrun "$oid" \
        "GitHub started no CI run on this head: a push while the pull request conflicts with its base starts none, and a base edit starts none. Close and reopen it, or push the branch again, then \`pr:land $number\`."
      ;;
  esac
}

# The CI depth gate (#5074), run first in a pull request's CI run: above the
# depth of one queue unit (`queue_unit_cap`, 3 when it reads nothing) the run
# is cancelled before any lane starts, so the runners go to the members that
# land next and to the merge groups. The pull request is told once a head;
# the watcher's promotion runs the run again once a landing moves it to that
# depth. A reading that fails runs the whole CI.
depth_limit() {
  local cap
  cap=$(queue_unit_cap 2> /dev/null) || cap=0
  (( cap > 0 )) || cap=3
  printf '%s\n' "$cap"
}
depth_gate() {
  local number=$1 head=$2 depth limit
  depth=$(stack_depth "$number") || return 0
  limit=$(depth_limit)
  (( depth > limit )) || return 0
  if ! depth_marked "$number" "$head"; then
    tell "$number" "pr-depth #$number waits at stack depth $depth" pr-depth "$head" \
      "Full CI runs for the bottom $limit pull requests of a stack only. This one is at depth $depth: its run stopped before any lane, and the landing watcher runs it again once a landing moves it to depth $limit."
  fi
  gh api --method POST "repos/$repo/actions/runs/$GITHUB_RUN_ID/cancel" > /dev/null || return 0
  # The cancellation ends this job; nothing after it runs meanwhile.
  sleep 300
}

if [[ ${1:-} == depth ]]; then
  depth_gate "${CI_PULL_REQUEST:?}" "${CI_HEAD:?}"
  exit 0
fi

# Sourced, the file gives its functions and runs nothing: `watcher.bash`
# runs `act_on` over its cases so (#5695).
[[ ${BASH_SOURCE[0]} == "$0" ]] || return 0
required=$(required_contexts)

# The run's GraphQL spend, read before and after from the free `rate_limit`
# endpoint and printed last, so a costly run shows in its own log.
spent_before=$(command gh api rate_limit --jq .resources.graphql.used 2> /dev/null) || spent_before=
trap 'if [[ -n $spent_before ]] && spent_after=$(command gh api rate_limit --jq .resources.graphql.used 2> /dev/null); then echo "landing: $((spent_after - spent_before)) GraphQL points this run"; fi' EXIT
used_refs=$(mktemp)
prs=$(read_prs)
actions=$(jq -c --argjson token "$token" '{token: $token, prs: .}' <<< "$prs" | jq -c -f "$pr_stack_dir/landing.jq")
err=$(mktemp)
while IFS= read -r action; do
  act_on "$action"
done < <(jq -c '.[]' <<< "$actions")

# The depth gate's promotion (#5074): a pull request the gate stopped that a
# landing has moved to the gate's depth or less runs its cancelled CI run
# again, and the gate passes it this time. One run listing and one rerun
# request each.
# The rerun goes through `RERUN_TOKEN`, the workflow's own token: the job
# grants it `actions: write`, and the fine-grained `LANDING_TOKEN` holds no
# Actions permission, so GitHub refuses it the rerun (HTTP 403).
limit=$(depth_limit)
while read -r number oid; do
  run=$(gh api "repos/$repo/actions/workflows/landing-checks.yml/runs?event=pull_request&head_sha=$oid&per_page=1" \
    --jq '.workflow_runs[0] | select(.conclusion == "cancelled") | .id') || continue
  [[ -n $run ]] || continue
  if GH_TOKEN=${RERUN_TOKEN:-$GH_TOKEN} gh api --method POST "repos/$repo/actions/runs/$run/rerun" > /dev/null 2> "$err"; then
    echo "#$number: at depth $limit or less; CI run $run runs again"
  else
    echo "::warning::#$number: the rerun of CI run $run failed: $(< "$err")"
  fi
done < <(jq -r --argjson limit "$limit" '.[] | select(.waiting and .depth <= $limit) | "\(.number) \(.oid)"' <<< "$prs")

# The landed heads no open pull request uses (#6185): GitHub keeps a stack
# member's branch while the member above has it as its base, and a branch a
# seat pushed with no pull request after its commits land elsewhere. One read
# of the remote heads over git, no GitHub API call, and one push that deletes
# the landed ones, each under a lease on the head as read. The checkout's own
# credential reads only, so the push carries `GH_TOKEN`, which may write
# contents. `LANDING_HEADS_DRY=true` prints the deletions and pushes nothing.
git fetch --quiet --no-tags origin "$trunk" || echo "::warning::fetching $trunk failed; the heads are read against the checkout's $trunk"
heads=$(branch_reading origin "origin/$trunk" "$used_refs" "${kept_branches[@]}") || heads='[]'
jq -r '.[] | select(.action == "delete") | "delete \(.name) at \(.oid[0:9]): \(.reason)"' <<< "$heads"
if [[ ${LANDING_HEADS_DRY:-false} != true ]] && jq -e 'any(.[]; .action == "delete")' <<< "$heads" > /dev/null; then
  auth=$(printf 'x-access-token:%s' "$GH_TOKEN" | base64 -w0)
  if ! GIT_CONFIG_COUNT=2 GIT_CONFIG_KEY_0=http.https://github.com/.extraheader GIT_CONFIG_VALUE_0= \
    GIT_CONFIG_KEY_1=http.https://github.com/.extraheader GIT_CONFIG_VALUE_1="AUTHORIZATION: basic $auth" \
    branch_delete origin "$heads"; then
    echo "::warning::the push that deletes the landed heads was refused in part; the next run reads them again"
  fi
fi
