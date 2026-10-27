#!/usr/bin/env bash
# The server-side landing watcher (#2701), run by `.github/workflows/landing.yml`
# on each `CI` completion, dequeue and draft taken back (#2984): one reading
# of every open pull request, decided by `landing.jq` and acted on with the
# stacking rule `pr:land` and `pr:watch` use (`stack.bash`). With the landing
# App's token (`LANDING_TOKEN_HELD` is `true`), a green pull request's stack
# is queued (`land_prefix`) and a dequeued stack restacked onto the trunk;
# without it, their seats are told.
# A red or conflicting pull request is its seat's. A seat is told by one
# comment per head, ending with the mark `<!-- landing:<event>:<head> -->`
# the next reading counts.
#
# The caller sets `GH_TOKEN` and, optionally, `LANDING_TOKEN_HELD`. A failed
# action is printed as a warning and the reading goes on: the next run reads
# the server again.
set -euo pipefail
repo=${GITHUB_REPOSITORY:-$(gh repo view --json nameWithOwner --jq .nameWithOwner)}
trunk=$(gh repo view "$repo" --json defaultBranchRef --jq .defaultBranchRef.name)
source "$(git rev-parse --show-toplevel)/.config/pr-stack/stack.bash"
token=${LANDING_TOKEN_HELD:-false}
required=$(required_contexts)

# The open pull requests, held ones left out (a draft, or the owner's
# `hold:owner`, #3253), as `landing.jq` reads them.
read_prs() {
  local pr
  gh api graphql --paginate -f owner="${repo%/*}" -f name="${repo#*/}" -f query='
    query($owner: String!, $name: String!, $endCursor: String) {
      repository(owner: $owner, name: $name) {
        pullRequests(states: OPEN, first: 20, after: $endCursor) {
          pageInfo { hasNextPage endCursor }
          nodes {
            number isDraft headRefOid isInMergeQueue mergeStateStatus
            autoMergeRequest { enabledAt }
            labels(first: 50) { nodes { name } }
            stack { number }
            author { __typename }
            commits(last: 1) { nodes { commit { statusCheckRollup { contexts(first: 100) { nodes {
              __typename
              ... on CheckRun { name status conclusion startedAt }
              ... on StatusContext { context state startedAt: createdAt } } } } } } }
            timelineItems(last: 1, itemTypes: [ADDED_TO_MERGE_QUEUE_EVENT, REMOVED_FROM_MERGE_QUEUE_EVENT, HEAD_REF_FORCE_PUSHED_EVENT, PULL_REQUEST_COMMIT]) { nodes { __typename } }
            comments(last: 100) { nodes { body } }
          }
        }
      }
    }' --jq '.data.repository.pullRequests.nodes[] | select((.isDraft or any(.labels.nodes[]; .name == "hold:owner")) | not)' \
    | while IFS= read -r pr; do
        jq -c --argjson reading "$(jq '.commits.nodes[0].commit.statusCheckRollup.contexts.nodes // []' <<< "$pr" \
          | jq -c --argjson required "$required" -f "$pr_stack_dir/required.jq")" \
          '{number, oid: .headRefOid,
            queued: (.isInMergeQueue or .autoMergeRequest != null),
            held: any(.labels.nodes[]; .name == "landing"),
            bot: (.author.__typename == "Bot"),
            stack: .stack.number,
            merge: .mergeStateStatus,
            reading: $reading,
            removed: (.timelineItems.nodes[0].__typename == "RemovedFromMergeQueueEvent"),
            marks: [.comments.nodes[].body | scan("<!-- landing:(pr-[a-z]+):([0-9a-f]{40}) -->") | "\(.[0]):\(.[1])"]}' <<< "$pr"
      done | jq -cs .
}

# Comment the event line `$2` on pull request `$1`, marked for its head `$4`
# as event `$3`, with the explanation `$5`.
tell() {
  gh pr comment "$1" -R "$repo" --body "$(printf '%s\n\n%s\n\n<!-- landing:%s:%s -->' "$2" "$5" "$3" "$4")" > /dev/null \
    || echo "::warning::#$1: the $3 comment failed"
}

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
      elif gh api -X PUT "repos/$repo/pulls/$number/update-branch" -f update_method=rebase -f expected_head_sha="$oid" > /dev/null 2> "$err"; then
        echo "#$number: GitHub rebases it onto its base"
        tell "$number" "pr-restacked #$number" pr-restacked "$oid" \
          "The merge queue removed this pull request with no red check in its stack; the landing watcher had GitHub rebase it onto its base. It lands once its checks are green."
      elif [[ $(jq -r .told <<< "$action") != true ]]; then
        echo "#$number: GitHub refused the rebase: $(< "$err")"
        tell "$number" "pr-dequeued #$number" pr-dequeued "$oid" \
          "The merge queue removed this pull request, and GitHub refused to rebase it onto its base: $(< "$err"). Rebase it, then \`pr:land $number\`."
      fi
      ;;
    green)
      tell "$number" "pr-green #$number" pr-green "$oid" \
        "Every required check passed on this head and the pull request is out of the merge queue: \`pr:land $number\` queues its stack's ready prefix."
      ;;
    dequeued)
      tell "$number" "pr-dequeued #$number" pr-dequeued "$oid" \
        "The merge queue removed this pull request at this head. Read the entry's run, then \`pr:land $number\`, which restacks it onto \`$trunk\`."
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
