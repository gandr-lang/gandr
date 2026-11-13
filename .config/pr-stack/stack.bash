# The stacking rule, mechanical (#1264), sourced by `pr:open`, `pr:land` and
# `pr:watch`. The server is the only record: every reading is of the open pull
# requests, and every stack is linked with `gh stack link`, which keeps no
# local state. Rebase order is the invariant: each branch sits on the one
# below it, and a restack moves the whole chain in one push.
#
# The caller sets `repo` (owner/name). `trunk` is the branch every lane lands
# on (`trunk.bash`, #5443).

pr_stack_dir="$(git rev-parse --show-toplevel)/.config/pr-stack"
# shellcheck source=trunk.bash
source "$pr_stack_dir/trunk.bash"
# shellcheck source=../gh/budget.bash
source "$pr_stack_dir/../gh/budget.bash"
# shellcheck source=../mise/host-lock.bash
source "$pr_stack_dir/../mise/host-lock.bash"
# shellcheck source=page.bash
source "$pr_stack_dir/page.bash"

# Refuse while `origin/$trunk` holds a change to the stacking rule the
# checked-out branch lacks (#1455). A task runs the rule from the branch it is
# run on, and a branch forked before a fix runs the rule the fix replaced:
# four pull requests opened from such branches stacked on a queued top and
# were moved to the trunk, one stack become three. Prints the missing commits.
stacking_current() {
  local behind
  git fetch --quiet origin "$trunk"
  behind=$(git log --no-merges --format='  %h %s' "HEAD..origin/$trunk" -- "$pr_stack_dir")
  if [[ -n "$behind" ]]; then
    printf 'the stacking rule changed on %s since this branch forked; rebase it onto origin/%s and run the task again:\n%s\n' "$trunk" "$trunk" "$behind" >&2
    return 1
  fi
}

# What every reading of a pull request takes, one GraphQL selection: its
# place in a stack, its holds, its merge and queue state, and its head's
# check rollup in the shape `gh pr view --json statusCheckRollup` gives.
# `pr:land` and `pr:await` poll through it (#5061), so it holds what their
# polls read: the merge commit and the queue position among them.
pr_fields='number state headRefName baseRefName isDraft createdAt isInMergeQueue mergeStateStatus mergeable headRefOid
  autoMergeRequest { enabledAt } labels(first: 50) { nodes { name } } stack { number } author { __typename }
  mergeCommit { oid } mergeQueueEntry { state position headCommit { oid } }
  timelineItems(last: 1, itemTypes: [REMOVED_FROM_MERGE_QUEUE_EVENT]) { nodes { ... on RemovedFromMergeQueueEvent { reason } } }
  commits(last: 1) { nodes { commit { committedDate statusCheckRollup { state contexts(first: 100) { nodes {
    __typename
    ... on CheckRun { name status conclusion startedAt detailsUrl checkSuite { workflowRun { databaseId } } }
    ... on StatusContext { context state startedAt: createdAt targetUrl } } } } } } }'

# Every open pull request, as a JSON array of `pr_fields`: one paginated
# query that every pull request reading on the host shares through the
# budget's cache (`budget.bash`), so a watch, a landing and a stacking
# asking at once cost one query between them. A page is 25 pull requests,
# 1 point (#5061): GitHub prices a page by the nodes it asks for, so a
# page of 100 costs 4 points whatever the number open.
pulls_reading() {
  gh api graphql --paginate -F owner='{owner}' -F name='{repo}' \
    -f query="query(\$owner: String!, \$name: String!, \$endCursor: String) { repository(owner: \$owner, name: \$name) { pullRequests(states: OPEN, first: 25, after: \$endCursor) { pageInfo { hasNextPage endCursor } nodes { $pr_fields } } } }" \
    --jq '.data.repository.pullRequests.nodes[]' \
    | jq -cs .
}

# Pull request `$1` as `pr_fields`: from `pulls_reading` while it is open,
# else read alone (a merged or closed one).
pr_reading() {
  local all found
  all=$(pulls_reading) || return 1
  found=$(jq -c --argjson n "$1" '.[] | select(.number == $n)' <<< "$all")
  if [[ -n $found ]]; then
    printf '%s\n' "$found"
    return
  fi
  gh api graphql -F owner='{owner}' -F name='{repo}' -F number="$1" \
    -f query="query(\$owner: String!, \$name: String!, \$number: Int!) { repository(owner: \$owner, name: \$name) { pullRequest(number: \$number) { $pr_fields } } }" \
    --jq '.data.repository.pullRequest'
}

# The check rollup of a pull request reading on stdin, as `required.jq`
# reads it.
rollup_of() {
  jq -c '.commits.nodes[0].commit.statusCheckRollup.contexts.nodes // []'
}

# The open pull requests, held ones among them, as a JSON array (`open.jq`).
open_prs() {
  pulls_reading | jq -c -f "$pr_stack_dir/open.jq"
}

# The open pull requests that land: the held ones, a draft or the owner's
# `hold:owner` (#3253), left out.
landable_prs() {
  open_prs | jq -c 'map(select(.hold == null))'
}

# The stack holding pull request `$1`, bottom to top (`chain.jq`).
server_stack() {
  landable_prs | jq -c --argjson n "$1" --arg trunk "$trunk" -f "$pr_stack_dir/chain.jq"
}

# Pull request `$1`'s depth in its stack (#5074): 1 on the trunk, one more
# for each open pull request below it.
stack_depth() {
  server_stack "$1" | jq -e --argjson number "$1" 'map(.number) | index($number) | values + 1'
}

# Whether pull request `$1` carries the depth gate's comment for head `$2`.
depth_marked() {
  gh api --paginate "repos/$repo/issues/$1/comments?per_page=100" --jq '.[].body' \
    | jq -e -s -R --arg mark "<!-- landing:pr-depth:$2 -->" 'contains($mark)' > /dev/null
}

# The open pull request a new one on branch `$1` stacks on (`top.jq`), or
# `null`.
stack_top() {
  landable_prs | jq -c --arg own "$1" --arg trunk "$trunk" -f "$pr_stack_dir/top.jq"
}

# The top a new pull request on branch `$1` stacks on, once no `pr:land` holds
# it (#1983): a held top is about to be queued, so the reading waits, every
# 15 seconds, for the hold to clear, and answers the top then, queued or not.
# The hold lasts while the landing waits on its prefix's required checks;
# after 30 minutes the wait gives up, naming the top.
await_top() {
  local top deadline=$((SECONDS + 1800))
  while :; do
    top=$(stack_top "$1")
    [[ $(jq -r '.held // false' <<< "$top") == true ]] || { printf '%s\n' "$top"; return; }
    (( SECONDS < deadline )) || { echo "the stack top #$(jq -r .number <<< "$top") has been held for landing for 30 minutes; run \`pr:open\` again once it is queued" >&2; return 2; }
    echo "the stack top #$(jq -r .number <<< "$top") is being landed; waiting for the hold to clear" >&2
    sleep 15
  done
}

# The commit the checked-out branch was last stacked on, recorded in the
# worktree's git directory as `gandr-stack-base` (#3877). A run that fails
# after it stacks leaves the old top's commits in the branch, and a top
# restacked since holds none of them by hash and may hold none by patch. The
# record names them still. Prints nothing when no record is kept, or when
# HEAD no longer carries the commit it names.
stack_base() {
  local record base
  record=$(git rev-parse --git-path gandr-stack-base)
  [[ -s $record ]] || return 0
  base=$(< "$record")
  if git merge-base --is-ancestor "$base" HEAD 2> /dev/null; then printf '%s\n' "$base"; fi
}

# Record `$1`, the commit the checked-out branch now stands on, as its stack
# base (`stack_base`, #3877).
record_stack_base() {
  git rev-parse "$1" > "$(git rev-parse --git-path gandr-stack-base)"
}

# Record the commit a new worktree starts from as its stack base (#5990):
# `wt:warm` runs it at creation. It writes only while the worktree records
# no base and `HEAD` is still a commit of `origin/$trunk`, so a rerun after
# the branch's own commits never moves the record onto them.
record_start() {
  [[ -z $(stack_base) ]] || return 0
  git merge-base --is-ancestor HEAD "origin/$trunk" 2> /dev/null || return 0
  record_stack_base HEAD
}

# The commit below the checked-out branch `$1`'s own commits, where its rebase
# onto the top's branch `$2` starts (#1298). Its own commits are those above
# `origin/$trunk` and the branch's stack base (`stack_base`, #3877) that no
# other open pull request's head holds and whose patch `origin/$2` does not
# already carry. A branch an earlier run stacked holds the commits of the top
# it was stacked on, and of any pull request that top has since been rebased
# off; neither is its own. Its own commits sit at its top, so the parent of
# the oldest is the fork. Prints `HEAD` when it holds none.
own_fork() {
  local heads=() head commit
  local -A held=()
  for head in $(open_prs | jq -r --arg own "$1" '.[] | select(.head != $own) | .head'); do
    git fetch --quiet origin "$head"
    heads+=("origin/$head")
  done
  mapfile -t -O "${#heads[@]}" heads < <(stack_base)
  # The patch comparison reads the top's side whole, so it runs apart from the
  # exclusion of the other heads.
  for commit in $(git rev-list --no-merges HEAD --not "origin/$trunk" "${heads[@]}"); do held[$commit]=1; done
  for commit in $(git rev-list --reverse --cherry-pick --right-only --no-merges "origin/$2...HEAD"); do
    if [[ -n "${held[$commit]:-}" ]]; then
      git rev-parse "$commit^"
      return
    fi
  done
  echo HEAD
}

# The trunk's changes the checked-out branch builds on that the top's branch
# `$1` lacks (#3654), one `<hash> <subject>` a line, oldest last: the trunk's
# first-parent commits after the top's merge base with it, up to the
# branch's. Prints nothing when the top holds every change the branch forked
# from.
trunk_lacked() {
  git log --first-parent --format='%h %s' \
    "$(git merge-base "origin/$1" "origin/$trunk")..$(git merge-base HEAD "origin/$trunk")"
}

# The commits of `$2` past `$1` whose change `$1` already holds (#4463), one
# subject a line, oldest first: the commits a rebase of `$2` onto `$1` drops.
# GitHub's own rebase (`update-branch`) replays each such commit as an empty
# one, with GitHub as its committer and none of the trailers the push rule
# requires, and every branch stacked above inherits it. The rebase runs
# detached in a scratch worktree, unsigned, with no ref updated whatever
# `rebase.updateRefs` says, and its result is discarded. Prints nothing when
# it conflicts: GitHub refuses that rebase itself.
upstream_replays() {
  local onto head scratch kept
  onto=$(git rev-parse "$1^{commit}")
  head=$(git rev-parse "$2^{commit}")
  scratch=$(mktemp -d "${TMPDIR:-/tmp}/gandr-replay-$$.XXXXXX")
  git worktree add --quiet --detach "$scratch" "$head"
  if git -C "$scratch" -c user.name=landing -c user.email=landing@invalid -c commit.gpgsign=false \
    rebase --quiet --no-update-refs "$onto" > /dev/null 2>&1; then
    kept=$(git -C "$scratch" log --reverse --format=%s "$onto..HEAD")
    git log --reverse --format=%s "$onto..$head" | awk -v kept="$kept" '
      BEGIN { count = split(kept, list, "\n"); for (i = 1; i <= count; i++) left[list[i]]++ }
      left[$0] > 0 { left[$0]--; next }
      { print }'
  else
    git -C "$scratch" rebase --abort 2> /dev/null || true
  fi
  git worktree remove --force "$scratch" 2> /dev/null || rm -rf "$scratch"
  git worktree prune
}

# Restack the stack of the top `$1`, a reading of `await_top`, onto the tip of
# `$trunk` when the top stands behind it (#6760). The merge queue's own
# landings move the trunk past an open top, and nothing else moves it: a
# branch stacked on it builds on a trunk that lacks each repair since, and
# its gate fails on a test the trunk already repairs (#6707 on #6759). So
# the stacking restacks the top's whole stack first (`tip_restack`). A stack
# that holds a queued member never moves (#2531), nor does a top held as a
# draft or one that conflicts with the trunk: `bound.jq` decides for them.
# A restack that stops pages the stack's lanes and the coordinator
# (`page_stopped`) and returns 1, so the branch opens on the trunk beside the
# top. Returns 2 when a reading fails. Prints what it did.
restack_behind() {
  local top=$1 number head state open stack out status=0
  number=$(jq -r .number <<< "$top")
  head=$(jq -r .head <<< "$top")
  git fetch --quiet origin "$trunk" "$head" || return 2
  git merge-base --is-ancestor "origin/$trunk" "origin/$head" && return 0
  state=$(top_reading "$number") || return 2
  jq -e '.queued or .draft or .merge == "DIRTY"' <<< "$state" > /dev/null && return 0
  open=$(landable_prs) || return 2
  stack=$(jq -c --argjson n "$number" --arg trunk "$trunk" -f "$pr_stack_dir/chain.jq" <<< "$open")
  [[ $stack != '[]' ]] || return 0
  jq -e --argjson stack "$stack" 'any(.[]; .landing and (.number | IN($stack[].number)))' <<< "$open" > /dev/null && return 0
  echo "the top #$number stands behind $trunk: its stack is restacked onto the tip first"
  out=$(tip_restack "$stack") || status=$?
  [[ -z $out ]] || printf '%s\n' "$out"
  (( status == 1 )) && page_stopped <<< "$out"
  return "$status"
}

# Stack the checked-out branch `$1` on the top `$2`, a reading of
# `await_top` or `null`, and leave the top it stacked on in `stacked_top`
# (#3654). With no top there is nothing to rebase. A top behind the trunk is
# restacked onto its tip first (`restack_behind`, #6760); when that restack
# stops, the branch opens on the trunk beside the top, and `stacked_past`
# names the top. Otherwise the branch's own
# commits (`own_fork`) are rebased onto the top's branch. That rebase
# conflicts when the top forked from the trunk before a change the own
# commits build on (`trunk_lacked`), though they apply to the trunk: the top
# carries the change only once it merges or its seat rebases it. A top bound
# for the trunk (`bound.jq`, #4124) is a future event, never a refusal
# (#4164): the stacking prints what it waits on and the line arming
# `pr:await` on the top (`arm_await`), and returns 3, so the seat's turn ends
# and the job wakes it. A top conflicting with the trunk past its seat's
# claim window is stacked past: the branch stacks on the highest pull request
# below it that does not conflict (`below_clean`), or on the trunk, and
# `stacked_past` names the top it went past. A top held or failed, and a
# conflict with the top's own changes, are refused, the first two naming the
# trunk's changes the top lacks.
stack_on_top() {
  local own=$1 base number fork lacked bound status
  stacked_top=$2
  stacked_past=
  while [[ $stacked_top != null ]]; do
    base=$(jq -r .head <<< "$stacked_top")
    number=$(jq -r .number <<< "$stacked_top")
    status=0
    restack_behind "$stacked_top" || status=$?
    if (( status == 2 )); then
      echo "a reading of the top #$number for its restack failed; run \`pr:open\` again" >&2
      return 1
    fi
    if (( status == 1 )); then
      echo "the restack of the top #$number stopped; $own opens on $trunk beside it"
      stacked_past=$number
      stacked_top=null
      break
    fi
    git fetch --quiet origin "$base" "$trunk"
    if git merge-base --is-ancestor "origin/$base" HEAD; then
      record_stack_base "origin/$base"
      return 0
    fi
    fork=$(own_fork "$own" "$base")
    if git rebase --quiet --update-refs --onto "origin/$base" "$fork" > /dev/null 2>&1; then
      record_stack_base "origin/$base"
      return 0
    fi
    git rebase --abort
    lacked=$(trunk_lacked "$base")
    if [[ -z $lacked ]]; then
      echo "the rebase of $own onto $base (#$number, the top) conflicts; resolve it on $own, run the hooks, and run \`pr:open\` again" >&2
      return 1
    fi
    bound=$(top_reading "$number" | jq -c --arg trunk "$trunk" -f "$pr_stack_dir/bound.jq")
    case $(jq -r .act <<< "$bound") in
      arm)
        printf 'the top #%s lacks these changes of %s the branch builds on, and %s; `pr:await %s` wakes the seat once it merges or holds them, and `pr:open` runs again then:\n%s\n' \
          "$number" "$trunk" "$(jq -r .why <<< "$bound")" "$number" "$(sed 's/^/  /' <<< "$lacked")"
        arm_await "$number"
        return 3
        ;;
      past)
        echo "the top #$number lacks $(wc -l <<< "$lacked") changes of $trunk the branch builds on, and $(jq -r .why <<< "$bound"); $own stacks past it"
        stacked_past=$number
        stacked_top=$(below_clean "$number")
        ;;
      *)
        printf 'the rebase of %s onto %s (#%s, the top) conflicts: the top lacks these changes of %s the branch builds on, and %s; run `pr:open` again once it merges or a newer top holds them:\n%s\n' \
          "$own" "$base" "$number" "$trunk" "$(jq -r .why <<< "$bound")" "$(sed 's/^/  /' <<< "$lacked")" >&2
        return 1
        ;;
    esac
  done
  # Past a top onto the trunk, the branch's own commits leave the top's.
  if [[ -n $stacked_past ]]; then
    fork=$(own_fork "$own" "$trunk")
    if ! git rebase --quiet --update-refs --onto "origin/$trunk" "$fork" > /dev/null 2>&1; then
      git rebase --abort
      echo "the rebase of $own onto $trunk, past #$stacked_past, conflicts; resolve it on $own, run the hooks, and run \`pr:open\` again" >&2
      return 1
    fi
    record_stack_base "origin/$trunk"
  fi
}

# Read the top again once the change is measured on the top `$2` from the
# fork `$3` (#3849): the checked-out branch `$1` stays on `$2`, or restacks
# onto a new top above it that changes none of its paths (`moved.jq`), and
# leaves the top it now stands on in `stacked_top`. A top restacked under
# the branch, gone, beside the fork or sharing a path is refused, as is a
# restack that conflicts.
restack_moved() {
  local own=$1 top=$2 fork=$3 now onto kept=true builds=false shared='[]' moved
  now=$(await_top "$own") || return 2
  stacked_top=$top
  if [[ $top != null ]]; then
    git fetch --quiet origin "$(jq -r .head <<< "$top")"
    git merge-base --is-ancestor "origin/$(jq -r .head <<< "$top")" HEAD || kept=false
  fi
  onto=$(jq -r '.head // empty' <<< "$now")
  if [[ -n $onto && $(jq -r .number <<< "$now") != $(jq -r '.number // empty' <<< "$top") ]]; then
    git fetch --quiet origin "$onto"
    if git merge-base --is-ancestor "$fork" "origin/$onto"; then builds=true; fi
    shared=$(comm -12 <(git diff --no-renames --name-only "$fork" "origin/$onto" | sort) \
      <(git diff --no-renames --name-only "$fork" HEAD | sort) | jq -R . | jq -sc .)
  fi
  moved=$(jq -nc --argjson top "$top" --argjson now "$now" --argjson kept "$kept" --argjson builds "$builds" --argjson shared "$shared" \
    '{top: $top, now: $now, kept: $kept, builds: $builds, shared: $shared}' | jq -c -f "$pr_stack_dir/moved.jq")
  case $(jq -r .act <<< "$moved") in
    stay) return 0 ;;
    refuse)
      echo "$(jq -r .why <<< "$moved"); run \`pr:open\` again" >&2
      return 2
      ;;
  esac
  if ! git rebase --quiet --update-refs --onto "origin/$onto" "$fork" > /dev/null 2>&1; then
    git rebase --abort
    echo "the stack top moved to #$(jq -r .number <<< "$now"), and the rebase of $own onto $onto conflicts; run \`pr:open\` again" >&2
    return 2
  fi
  record_stack_base "origin/$onto"
  stacked_top=$now
  echo "the stack top moved to #$(jq -r .number <<< "$now") while the obligations were measured; $own restacks onto it, its own change measured as it was"
}

# The revision the checked-out change is measured from (#3148), on a trunk
# fetched first: a pull request below that merged since the seat last
# fetched is the trunk's, never read as this change's own paths. A branch an
# earlier run stacked carries its old top's commits, and the top's head may
# have moved since, so `evidence:base` no longer names it. The recorded stack
# base (`stack_base`, #3877) still does, and it measures from there when it
# lies past what `evidence:base` names (#4064). A new worktree records the
# commit it starts from (`.config/wt.toml`, #5990), so a branch cut from a
# `landing` that the landing rebase rewrites since measures from that commit.
measured_from() {
  local base stacked
  git fetch --quiet origin "$trunk"
  base=$(evidence_base)
  stacked=$(stack_base)
  if [[ -n $stacked ]] && git merge-base --is-ancestor "$base" "$stacked"; then base=$stacked; fi
  printf '%s\n' "$base"
}

# The fork of the own commits of `$1`, a fetched ref, on a trunk that the
# landing rebase rewrote since `$1` was cut from it (#5990, #6399). A head on
# the old lineage carries commits that `origin/$trunk` holds by patch under
# other hashes, which `git cherry` marks `-`. A head that is only behind the
# trunk carries none. The fork is the newest commit past `origin/$trunk` that
# the rebase noted under `refs/notes/rebased`, the old tip, or else the newest
# commit that the trunk holds by patch. Prints the fork and the count of the
# held commits, separated by a tab, or nothing for a head that is only behind.
rewritten_fork() {
  local cherry held fork='' commit
  git fetch --quiet origin "$trunk"
  cherry=$(git cherry "origin/$trunk" "$1")
  held=$(grep -c '^-' <<< "$cherry" || true)
  (( held > 0 )) || return 0
  git fetch --quiet origin '+refs/notes/rebased:refs/notes/rebased' 2> /dev/null || true
  for commit in $(git rev-list "$1" --not "origin/$trunk"); do
    if git notes --ref=rebased show "$commit" > /dev/null 2>&1; then
      fork=$commit
      break
    fi
  done
  [[ -n $fork ]] || fork=$(awk '$1 == "-" { last = $2 } END { print last }' <<< "$cherry")
  printf '%s\t%s\n' "$fork" "$held"
}

# Refuse a branch with no recorded stack base that carries commits
# `origin/$trunk` holds by patch (#5990). The landing rebase rewrites the
# trunk: a branch cut from the old tip keeps the old commits under their old
# hashes, and its merge base falls back to an old commit of `main`. So
# `evidence:base` would read every old commit as the branch's own change.
# The refusal names the fork that `rewritten_fork` reads. Prints the refusal
# and returns 1, or prints nothing.
rewritten_base() {
  local lineage fork held
  [[ -z $(stack_base) ]] || return 0
  lineage=$(rewritten_fork HEAD)
  [[ -n $lineage ]] || return 0
  IFS=$'\t' read -r fork held <<< "$lineage"
  printf '%s carries %s commit(s) that origin/%s holds by patch, and its worktree records no stack base: a rewrite of %s left them under its own commits, so every one would read as its change. Replay its own commits with `git rebase --onto origin/%s %s`, then run the task again\n' \
    "$(git branch --show-current)" "$held" "$trunk" "$trunk" "$trunk" "${fork:0:12}"
  return 1
}

# The commit `pr:land` reads pull request `$3`'s change from, its base branch
# `$1` and its head `$2` fetched (#6055, #6062): the merge base of the two,
# unless the worktree is on `$2` and records a stack base that `$1` does not
# hold. `pr:open` stacks a branch on the head of the pull request below and
# records that head. On `$trunk`, a pull request below that the queue holds
# stays open under that head, and GitHub links no stack to it. The merge base
# then falls below its commits, so the change is read from the record, and the
# pull request owes only its own commits' rows. A record that no other open
# pull request carries, or that a base other than `$trunk` does not hold, is
# an old copy of the pull request below: a seat amended it, or the queue
# merged it under new hashes. Every reading from the merge base would take that
# copy's change as this one's, so the refusal names the replay. One REST call
# reads the record's open pull requests, only when the base is `$trunk` and
# does not hold the record. Prints the commit, or the refusal and returns 1.
change_base() {
  local base=$1 head=$2 number=$3 stacked=
  if [[ $(git rev-parse HEAD) == "$(git rev-parse --verify --quiet "origin/$head")" ]]; then stacked=$(stack_base); fi
  if [[ -z $stacked ]] || git merge-base --is-ancestor "$stacked" "origin/$base"; then
    git merge-base "origin/$base" "origin/$head"
    return
  fi
  if [[ $base == "$trunk" ]] && [[ -n $(gh api "repos/$repo/commits/$stacked/pulls" --jq "[.[] | select(.state == \"open\" and .number != $number) | .number] | first // empty" 2> /dev/null) ]]; then
    printf '%s\n' "$stacked"
    return
  fi
  printf '%s stands on %s, which origin/%s no longer holds and no other open pull request carries: the pull request below was amended or merged under new hashes, and its old commits under this change would read as its own. Replay the own commits with `git rebase --onto origin/%s %s`, push, then run the task again\n' \
    "$head" "${stacked:0:12}" "$base" "$base" "${stacked:0:12}"
  return 1
}

# `evidence:base`, the measurement `measured_from` takes once the trunk is
# fetched; `fetched-base.bash` reads it as the merge base it falls back to.
evidence_base() { mise run --quiet evidence:base; }

# Whether pull request `$1` is in the merge queue or set to enter it on its
# own (auto-merge). Either way it lands alone, and GitHub refuses to link it
# into a stack.
in_queue() {
  pr_reading "$1" | jq '.isInMergeQueue or .autoMergeRequest != null'
}

# What `bound.jq` reads of pull request `$1`: whether it is queued or set to
# enter the queue, whether it is a draft, its merge state, its head's check
# rollup and the seconds since its head commit was made, as one JSON object.
top_reading() {
  pr_reading "$1" \
    | jq -c '{queued: (.isInMergeQueue or .autoMergeRequest != null), draft: .isDraft, merge: .mergeStateStatus, checks: (.commits.nodes[0].commit.statusCheckRollup.state // null), age: (now - (.commits.nodes[0].commit.committedDate | fromdateiso8601) | floor)}'
}

# The line a seat's harness arms `pr:await $1` on (#4164, `await.jq`).
arm_await() {
  jq -nr --argjson n "$1" -L "$pr_stack_dir" 'include "await"; arm($n)'
}

# The highest pull request below `$1` in its stack that does not conflict
# with the trunk, `{number, head}`, or `null` (#4164): where a branch stacks
# past a top no seat rebases.
below_clean() {
  local member
  for member in $(server_stack "$1" | jq -c --argjson n "$1" '(map(.number) | index($n)) as $at | .[: $at] | reverse[]'); do
    if [[ $(top_reading "$(jq -r .number <<< "$member")" | jq -r .merge) != DIRTY ]]; then
      printf '%s\n' "$member"
      return
    fi
  done
  echo null
}

# The numbers of the stack `$1`'s pull requests in the merge queue, as a JSON
# array.
queued_of() {
  pulls_reading | jq -c --argjson stack "$1" \
    'map(select(.isInMergeQueue or .autoMergeRequest != null) | .number) as $queued | [$stack[].number | select(IN($queued[]))]'
}

# The number of the server stack pull request `$1` belongs to, `null` when
# none. GitHub keeps a stack's merged members, so a pull request whose stack
# below it merged still belongs to it.
stack_of() {
  pr_reading "$1" | jq -r '.stack.number // "null"'
}

# The members of the server stack pull request `$1` belongs to, bottom to
# top, as a JSON array of `{number, state, isInMergeQueue}`; empty when it
# belongs to none.
stack_entries() {
  gh api graphql -F owner='{owner}' -F name='{repo}' -F number="$1" \
    -f query='query($owner: String!, $name: String!, $number: Int!) { repository(owner: $owner, name: $name) { pullRequest(number: $number) { stack { entries(first: 100) { nodes { pullRequest { number state isInMergeQueue } } } } } } }' \
    --jq '[.data.repository.pullRequest.stack.entries.nodes[]?.pullRequest]'
}

# Link the open chain `$1` on the server (`link.jq`): into the stack a member
# already belongs to, by that stack's number, so the stack's merged members
# stay below the open ones (#1275); otherwise as a new stack. GitHub keeps a
# member closed unmerged as well, and refuses every later link onto its
# stack (#2094), so such a stack is unstacked first: GitHub leaves its queued
# and auto-merge members stacked, and drops the rest, the closed one among
# them. The stack's number is read again from a member it kept, if any, and
# the open members it dropped are linked again with the chain. A stack that
# holds an open member the chain leaves out, while the chain adds a member,
# is unstacked first too: the link appends the new members above every
# member of the stack, so the new members stand above the one left out, as
# above a held draft that `pr:open` stacks past (#7142, `unstack.jq`). The
# entries of a server stack are read once, for its first member in the chain.
# Every member of that stack then takes the stack its first member settled,
# since they all share its entries (#5671). A chain that takes no arguments,
# one pull request in no stack, is linked nothing (#3817).
stack_link() {
  local number stack server entries kept stacks=() args chain
  local -A settled=()
  chain=$(jq -c 'map(.number)' <<< "$1")
  for number in $(jq -r '.[]' <<< "$chain"); do
    stack=$(stack_of "$number")
    if [[ $stack != null && -n ${settled[$stack]+set} ]]; then
      stack=${settled[$stack]}
    elif [[ $stack != null ]]; then
      server=$stack
      entries=$(stack_entries "$number")
      if [[ $(printf '%s\n%s\n' "$chain" "$entries" | jq -s -f "$pr_stack_dir/unstack.jq") == true ]]; then
        # It exits nonzero (5) whenever it leaves a queued member stacked;
        # a stack it failed to clear fails the link below, which says so.
        gh stack unstack "$stack" < /dev/null > /dev/null 2>&1 || :
        stack=null
        for kept in $(jq -r '.[] | select(.state == "OPEN") | .number' <<< "$entries"); do
          stack=$(stack_of "$kept")
          [[ $stack == null ]] || break
        done
      fi
      settled[$server]=$stack
    fi
    stacks+=("$stack")
  done
  mapfile -t args < <(jq -cn --argjson chain "$(jq -c 'map(.number)' <<< "$1")" \
    '{chain: $chain, stacks: ($ARGS.positional | map(fromjson))}' --args "${stacks[@]}" | jq -r -f "$pr_stack_dir/link.jq")
  (( ${#args[@]} > 0 )) || return 0
  # No prompt is answered here: a question fails the link instead of waiting.
  # The link bases the chain's bottom on the branch `--base` names. With no
  # `--base`, it uses GitHub's default branch, which is not the trunk (#5443).
  gh stack link --base "$trunk" "${args[@]}" < /dev/null > /dev/null
}

# Rebase the stack `$1` (bottom to top) onto `origin/$trunk` and push every
# branch it moved, in one atomic push leased on each branch's remote tip. The
# rebase runs in a scratch worktree, detached, so no seat's checkout is
# touched: a branch checked out in another worktree moves on the server, and
# its seat's next fetch reads it. Prints one line per branch that moved.
# Stops at a conflict, naming the branch and its conflicting files, with
# nothing pushed. Only the stack's own commits are replayed. A bottom branch
# still carrying commits of a pull request merged below it, as its earlier
# heads held them, is replayed from the newest such head (`landed_fork`,
# #3078), so a lower pull request restacked or squashed before it merged
# leaves nothing of its own to conflict. A branch that does not contain the
# open one below it, because that one was force-pushed since (#3115), is
# replayed from the newest head of the lower it holds (`relink_fork`); a
# branch holding none of them is refused. The replay is `chain_replay`'s,
# member by member, and git signs every commit it writes (#3745). Before the
# push, the replay runs the check of each generated artifact a member's move
# makes due (`replay_reads`, #6144), and a stale one stops the restack with
# nothing pushed. The scratch
# is named for this process (`gandr-scratch-<pid>.`), and the caller's exit
# trap runs `drop_scratch`, so a failure anywhere removes it; a scratch a hard
# kill leaves, its process gone, is `wt:sweep`'s.
restack() {
  local stack=$1 heads head below fork merged held scratch line conflicted i status=0 members=() relinked=() moved=() pushes=() leases=() old new
  mapfile -t heads < <(jq -r '.[].head' <<< "$stack")
  git fetch --quiet origin "$trunk" "${heads[@]}"
  merged=$(git merge-base "origin/${heads[0]}" "origin/$trunk")
  fork=$(landed_fork "${heads[0]}" "$merged")
  if [[ $fork != "$merged" ]]; then
    echo "${heads[0]}: $(git rev-list --count "$merged..$fork") commits a merged pull request below held are left out"
  fi
  members=("${heads[0]}")
  for (( i = 1; i < ${#heads[@]}; i++ )); do
    head=${heads[i]}
    below=${heads[i-1]}
    if git merge-base --is-ancestor "origin/$below" "origin/$head"; then
      members+=("$head")
      continue
    fi
    held=$(relink_fork "$below" "$(git rev-parse "origin/$head")")
    if [[ -z $held ]]; then
      echo "$head does not contain $below, the branch below it, nor any of its earlier heads; rebase it onto $below first" >&2
      return 1
    fi
    echo "$head: $(git rev-list --count "$held..origin/$head") commits replayed from $below's earlier head ${held::12} onto its current one"
    members+=("$head:$held")
    relinked+=("$head")
  done
  scratch=$(mktemp -d "${TMPDIR:-/tmp}/gandr-scratch-$$.XXXXXX")
  pr_stack_scratch=$scratch
  git worktree add --quiet --detach "$scratch" "origin/${heads[-1]}"
  if ! chain_replay "$scratch" "origin/$trunk" "$fork" git "${members[@]}"; then
    conflicted=${heads[chain_stop]}
    if [[ -n $chain_files && " ${relinked[*]} " == *" $conflicted "* ]]; then
      echo "the replay of $conflicted onto ${heads[chain_stop-1]} conflicts ($chain_files); rebase $conflicted onto ${heads[chain_stop-1]} by hand and land again" >&2
    elif [[ -n $chain_files ]]; then
      echo "the restack of ${heads[*]} onto origin/$trunk conflicts in $conflicted ($chain_files); rebase $conflicted onto origin/$trunk by hand and land again" >&2
    fi
    status=1
  fi
  if (( status == 0 )); then
    for line in "${chain_moved[@]}"; do
      read -r head old new <<< "$line"
      [[ "$old" != "$new" ]] || continue
      pushes+=("$new:refs/heads/$head")
      leases+=("--force-with-lease=refs/heads/$head:$old")
      moved+=("$head ${old::12}..${new::12}")
    done
    if (( ${#pushes[@]} > 0 )); then
      git -C "$scratch" push --quiet --atomic "${leases[@]}" origin "${pushes[@]}" || status=$?
      gh_budget_stale
    fi
  fi
  drop_scratch
  (( status == 0 )) || return "$status"
  if (( ${#moved[@]} > 0 )); then printf 'moved %s\n' "${moved[@]}"; fi
  git fetch --quiet origin "${heads[@]}"
}

# The open stacks after a push that moves `$trunk` from outside the merge
# queue (#6700): the landing rebase, a hold or a repair by hand. Each stack
# whose bottom stands on the trunk and lacks its new tip is restacked onto it
# (`restack`), its own commits replayed in one atomic push. Otherwise every
# lane that opens next waits on a top that nothing moves (`bound.jq`, #3654).
# A member in the merge queue never moves (#2531). So the act waits for it
# as `pr:watch`'s heal does (`heal.jq`): it reads the stacks again every
# `TRUNK_MOVED_POLL` seconds, 30 by default, for at most `TRUNK_MOVED_WAIT`
# seconds, 600 by default. After that it leaves the stack to the heal, and
# the queue builds its group on the new tip itself. A restack that conflicts
# or fails pushes nothing. Prints one line for each stack, and for a restack
# that stops, `stopped <number>… [<lane>…]: <the reason>`. Returns 3 when a
# restack stops, 1 when a reading fails, and 0 otherwise. The caller's exit
# trap runs `drop_scratch`.
trunk_moved() {
  local deadline poll open bottom stack numbers queued status=0
  local -a bottoms
  deadline=$((SECONDS + ${TRUNK_MOVED_WAIT:-600}))
  poll=${TRUNK_MOVED_POLL:-30}
  git fetch --quiet origin "$trunk" || return 1
  gh_budget_stale
  open=$(landable_prs) || return 1
  mapfile -t bottoms < <(jq -r --arg trunk "$trunk" '.[] | select(.base == $trunk and (.bot | not)) | .number' <<< "$open")
  for bottom in "${bottoms[@]}"; do
    while :; do
      jq -e --argjson n "$bottom" 'any(.[]; .number == $n)' <<< "$open" > /dev/null || continue 2
      stack=$(jq -c --argjson n "$bottom" --arg trunk "$trunk" -f "$pr_stack_dir/chain.jq" <<< "$open")
      numbers=$(jq -r 'map("#\(.number)") | join(" ")' <<< "$stack")
      queued=$(jq -r --argjson stack "$stack" '[.[] | select(.landing and (.number | IN($stack[].number))) | "#\(.number)"] | join(" ")' <<< "$open")
      [[ -n $queued ]] || break
      if (( SECONDS >= deadline )); then
        echo "stack $numbers: $queued stays in the merge queue, and its pr:watch heals the stack once it lands"
        continue 2
      fi
      sleep "$poll"
      gh_budget_stale
      open=$(landable_prs) || return 1
    done
    tip_restack "$stack" || { (( $? == 2 )) && return 1; status=3; }
  done
  return "$status"
}

# Restack the open stack `$1` (`chain.jq`'s, bottom to top) onto the tip of
# `$trunk` (`restack`) when its bottom lacks the tip (#6700, #6760). Prints
# one line for the stack: it stands on the tip, it is restacked, or
# `stopped <number>… [<lane>…]: <the reason>`, the line `page_stopped`
# pages. A restack that stops pushes nothing. Returns 1 when it stops, and 2
# when a fetch fails.
tip_restack() {
  local stack=$1 numbers head lanes out
  numbers=$(jq -r 'map("#\(.number)") | join(" ")' <<< "$stack")
  head=$(jq -r '.[0].head' <<< "$stack")
  git fetch --quiet origin "$trunk" "$head" || return 2
  if git merge-base --is-ancestor "origin/$trunk" "origin/$head"; then
    echo "stack $numbers: stands on the tip of $trunk"
    return 0
  fi
  if out=$(restack "$stack" 2>&1); then
    echo "stack $numbers: restacked onto $(git rev-parse --short "origin/$trunk")"
    [[ -z $out ]] || printf '%s\n' "$out"
    return 0
  fi
  lanes=$(jq -r 'map(.head | split("-")[0]) | unique | join(" ")' <<< "$stack")
  echo "stopped $numbers [$lanes]: $(paste -sd ' ' - <<< "$out")"
  return 1
}

# The first member of the chain `$2`… (branches, bottom to top, fetched)
# whose remote tip does not hold the tip below it, the first member's below
# being the commit `$1` (#5071, #5695). Prints the member's index and fails,
# or prints nothing when each member holds the one below it. A replay of such
# a chain leaves the member its old commits, so `restack_past` and
# `cut_closed` refuse it.
chain_gap() {
  local below=$1 head i=0
  shift
  for head in "$@"; do
    if ! git merge-base --is-ancestor "$below" "origin/$head"; then
      echo "$i"
      return 1
    fi
    below=origin/$head
    i=$((i + 1))
  done
}

# Replay the chain `$5`… (branches, bottom to top, fetched) in the scratch
# worktree `$1`, member by member (#5749). Each member's own commits, those
# past the old tip below it (`$3` for the first), go onto the new tip below it
# (`$2` for the first). A member written `<branch>:<commit>` replays from that
# commit in place of the old tip below it, as `restack` gives a member that
# `relink_fork` relinks; a branch name holds no `:`. `$4` names the signer.
# With `git`, the rebase signs each commit it writes (`--gpg-sign`, #3745),
# and the caller pushes the new tips. With `github`, the rebase writes its
# commits as `landing`, and `signed_replay` moves each branch to commits that
# GitHub signs (#5214), because a runner holds no signing key. A member whose
# rebase leaves its tip as it was is not replayed. Before a member moves,
# `replay_reads` reads the generated artifacts its replay can leave stale
# (#6144, #6159). Its old base is where its own commits start: the merge base
# of the old tip below it and its old head. Sets `chain_moved` to one
# `<branch> <old> <new>` for each member replayed, `<new>` equal to `<old>`
# for a tip that did not move. At a conflict, a refused replay or a stale
# artifact it stops and fails. Then `chain_stop` is the index of the member
# that stopped, and `chain_files` the files that conflict, empty when no file
# conflicts. A rebase that stops on no conflict prints git's error. The
# members replayed before the stop stay replayed.
chain_moved=()
chain_stop=
chain_files=
chain_replay() {
  local dir=$1 onto=$2 from=$3 signer=$4 member head old tip new error i=0
  local -a rebase=(rebase --quiet --gpg-sign)
  shift 4
  [[ $signer == git ]] || rebase=(-c user.name=landing -c user.email=landing@users.noreply.github.com rebase --quiet)
  chain_moved=()
  chain_stop=
  chain_files=
  for member in "$@"; do
    head=${member%%:*}
    [[ $member == "$head" ]] || from=${member#*:}
    old=$(git rev-parse "origin/$head")
    git -C "$dir" checkout --quiet --detach "$old"
    if ! error=$(git -C "$dir" "${rebase[@]}" --onto "$onto" "$from" 2>&1 > /dev/null); then
      chain_stop=$i
      chain_files=$(git -C "$dir" diff --name-only --diff-filter=U | paste -sd ' ' -)
      [[ -n $chain_files ]] || printf '%s\n' "$error" >&2
      git -C "$dir" rebase --abort 2> /dev/null || :
      return 1
    fi
    tip=$(git -C "$dir" rev-parse HEAD)
    new=$tip
    if [[ $tip != "$old" ]] && ! replay_reads "$dir" "$(git merge-base "$from" "$old")" "$onto" "$tip" "$signer" "$head"; then
      chain_stop=$i
      return 1
    fi
    if [[ $signer == github && $tip != "$old" ]]; then
      new=$(signed_replay "$head" "$onto" "$tip" "$old") || { chain_stop=$i; return 1; }
      git fetch --quiet origin "$head"
    fi
    chain_moved+=("$head $old $new")
    onto=$new
    from=$old
    i=$((i + 1))
  done
}

# Whether the replay of branch `$6` from the old base `$2` onto the new base
# `$3`, as the tip `$4` in the scratch `$1`, keeps each generated artifact
# (#6144). With the signer `$5` `git`, on a seat, `stale.bash` runs the check
# of each row the replay makes due, and the checks build in the caller's
# target directory. With `github`, on a runner, which builds no crate within
# the hosted budget, `stale.bash --due` reads the due rows alone. A due row
# holds the branch, and a seat's `pr:land` replays it with the checks
# (#6159). Fails, naming each stale or due artifact on stderr. A check that
# fails on its own (`stale.bash` exits 2, #6786) reads nothing, so the replay
# cannot read the artifacts, and the message says so, not that they are stale.
replay_reads() {
  local dir=$1 old=$2 new=$3 tip=$4 signer=$5 head=$6 script target out rows status=0
  script=$pr_stack_dir/../replay/stale.bash
  if [[ $signer == git ]]; then
    target=$(git rev-parse --show-toplevel)/target
    out=$(cd "$dir" && CARGO_TARGET_DIR=$target "$script" "$old" "$new" "$tip" 2>&1) || status=$?
    (( status != 0 )) || return 0
    if (( status == 1 )); then
      echo "the replay of $head leaves generated artifacts stale, as below; nothing is pushed" >&2
    else
      echo "the replay of $head cannot read its generated artifacts, since a check fails on its own, as below; nothing is pushed" >&2
    fi
    printf '%s\n' "$out" >&2
    return 1
  fi
  rows=$(cd "$dir" && "$script" --due "$old" "$new" "$tip" | jq -r 'map(.name) | join("; ")') || return 1
  [[ -n $rows ]] || return 0
  echo "the replay of $head makes due: $rows; a runner builds none of their checks, so the branch is held for a seat's \`mise run pr:land\`, which runs them" >&2
  return 1
}

# Cut the red member `$2` out of the stack `$1` (bottom to top), and restack
# the members above it past it (#4642): their own commits are replayed onto
# the member below it, or onto `origin/$trunk` when it is the bottom, and the
# red member's commits are left out. Each member's remote tip from the red one
# up must hold the one below it (`chain_gap`), or the replay leaves a member
# its old commits (#5071): such a stack is refused, both members named. The
# replay runs in a scratch worktree and signs every commit it writes
# (`chain_replay`), so a conflict stops the cut with nothing moved. The
# server refuses a base edit on a stacked pull request, so the stack is
# unstacked first and the member above the red one retargeted onto the red
# one's base, read against its replayed head (`set_base`, #6797). The server
# is then read again, and only a reading with the red member in no stack and
# the member above it on that base lets the push run (#5071): every moved
# branch in one atomic push leased on each remote tip. A read or a push that
# fails after the base edit sets the old base again, so the base never moves
# without the branch (#6797). The chain without the red member is then
# linked again (`stack_link`). The red member stays open on its base for its
# seat. Prints one line per branch that moved.
restack_past() {
  local stack=$1 red=$2 at heads above head onto base scratch server held gap line status=0 pushes=() leases=() moved=() old new number tip edited=0
  at=$(jq --argjson red "$red" 'map(.number) | index($red)' <<< "$stack")
  mapfile -t heads < <(jq -r '.[].head' <<< "$stack")
  above=("${heads[@]:at+1}")
  (( ${#above[@]} > 0 )) || return 0
  git fetch --quiet origin "$trunk" "${heads[@]}"
  if (( at == 0 )); then base=$trunk; else base=${heads[at-1]}; fi
  onto=origin/$base
  if ! gap=$(chain_gap "origin/${heads[at]}" "${above[@]}"); then
    echo "${above[gap]} does not contain ${heads[at+gap]}, the member below it; rebase it onto ${heads[at+gap]} first" >&2
    return 1
  fi
  scratch=$(mktemp -d "${TMPDIR:-/tmp}/gandr-scratch-$$.XXXXXX")
  pr_stack_scratch=$scratch
  git worktree add --quiet --detach "$scratch" "origin/${heads[-1]}"
  if ! chain_replay "$scratch" "$onto" "origin/${heads[at]}" git "${above[@]}"; then
    [[ -z $chain_files ]] || echo "the restack of ${above[*]} past #$red onto $onto conflicts ($chain_files); land again once #$red is fixed" >&2
    status=1
  fi
  if (( status == 0 )); then
    for line in "${chain_moved[@]}"; do
      read -r head old new <<< "$line"
      pushes+=("$new:refs/heads/$head")
      leases+=("--force-with-lease=refs/heads/$head:$old")
      moved+=("$head ${old::12}..${new::12}")
      [[ $head != "${above[0]}" ]] || tip=$new
    done
    number=$(jq -r ".[$at + 1].number" <<< "$stack")
    server=$(stack_of "$red")
    # It exits nonzero (5) whenever it leaves a queued member stacked, so
    # the server's reading below decides, never its exit.
    [[ $server == null ]] || gh stack unstack "$server" < /dev/null > /dev/null 2>&1 || :
    if set_base "$number" "$base" "$tip"; then edited=1; else status=1; fi
  fi
  if (( status == 0 )); then
    server=$(stack_of "$red") || status=$?
    held=$(pr_reading "$number" | jq -r '.baseRefName') || status=$?
    if (( status == 0 )) && [[ $server != null ]]; then
      echo "the server still holds #$red in stack $server after the unstack; nothing is pushed" >&2
      status=1
    elif (( status == 0 )) && [[ $held != "$base" ]]; then
      echo "the server holds #$number on $held, not $base, after the base edit; nothing is pushed" >&2
      status=1
    fi
  fi
  if (( status == 0 )); then
    git -C "$scratch" push --quiet --atomic "${leases[@]}" origin "${pushes[@]}" || status=$?
    gh_budget_stale
  fi
  if (( status != 0 && edited == 1 )); then
    gh pr edit "$number" -R "$repo" --base "${heads[at]}" > /dev/null \
      || echo "#$number stands on $base with its branch unmoved: set its base to ${heads[at]} by hand" >&2
  fi
  if (( status == 0 )); then
    stack_link "$(jq -c --argjson red "$red" 'map(select(.number != $red))' <<< "$stack")" || status=$?
  fi
  drop_scratch
  (( status == 0 )) || return "$status"
  printf 'moved %s\n' "${moved[@]}"
  git fetch --quiet origin "${above[@]}"
}

# The red reading of pull request `$1` (#5073), as `{check, run}`: the merge
# queue removed it for `failed_checks`, named by the first failed job of its
# newest failed merge-group run; else a required check that concluded
# `failure` at its head (`red.jq`). Prints `null` when it is not red. The
# caller sets `required` (`required_contexts`).
red_reading() {
  local number=$1 view group run
  view=$(pr_reading "$number") || return 1
  if [[ $(queue_removal "$number") == failed_checks ]]; then
    group="gh-readonly-queue/$trunk/pr-$number-"
    run=$(gh api "repos/$repo/actions/runs?event=merge_group&status=failure&per_page=100" \
      --jq '[.workflow_runs[] | {id, head_branch, html_url}]' \
      | jq -c --arg group "$group" 'map(select(.head_branch | startswith($group))) | first // null') || return 1
    if [[ $run == null ]]; then
      jq -cn '{check: "the merge queue", run: null}'
      return
    fi
    gh api "repos/$repo/actions/runs/$(jq -r .id <<< "$run")/jobs?filter=latest&per_page=100" \
      --jq '[.jobs[] | select(.conclusion == "failure") | .name] | first // "the merge queue"' \
      | jq -cR --arg run "$(jq -r .html_url <<< "$run")" '{check: ., run: $run}'
    return
  fi
  rollup_of <<< "$view" | jq -c --argjson required "$required" -f "$pr_stack_dir/red.jq"
}

# Cut the red bottom `$1` out of its server stack and place it on the top
# (#5073), through `cut_to_top` with each red member flagged. Prints nothing
# when `$1` is not a red bottom with members above it. Prints `<stack
# before>\t<stack after>\t<check>\t<run>` on a cut. Fails naming the reason on
# stderr, with nothing moved, when the cut is refused or conflicts.
cut_bottom() {
  local root=$1 red stack member flagged cut
  red=$(red_reading "$root") || return 1
  [[ $red != null ]] || return 0
  stack=$(server_stack "$root")
  [[ $(jq --argjson root "$root" 'length > 1 and .[0].number == $root' <<< "$stack") == true ]] || return 0
  flagged=("$root")
  for member in $(jq -r '.[1:][].number' <<< "$stack"); do
    [[ $(red_reading "$member") == null ]] || flagged+=("$member")
  done
  cut=$(cut_to_top "$root" "$stack" "$(printf '%s\n' "${flagged[@]}" | jq -sc .)") || return
  printf '%s\t%s\t%s\n' "$cut" "$(jq -r .check <<< "$red")" "$(jq -r '.run // "no run"' <<< "$red")"
}

# Cut the member `$1` out of the server stack `$2` (bottom to top) and place
# it on the top (#5073, #5902). `$3` is a JSON array of the members flagged:
# a red one for `cut_bottom`, the held one for `pr:hold`. `heal.jq` decides
# the cut as `pr:watch`'s heal does: no member above changes a path `$1`
# changes, none is flagged and none is queued. `restack_past` then replays
# the members above onto the member below `$1`, or the trunk, signed, with
# #5071's server and ancestry checks. `$1` is retargeted onto the new top and
# linked there, so it lands last once its seat clears it. Then the runs the
# cut made stale are cancelled (`cancel_stale`). One cut runs at a time on
# the host, under the `stack-cut` lock on descriptor 7. Prints `<stack
# before>\t<stack after>` on a cut. Fails naming the reason on stderr, with
# nothing moved, when the cut is refused, waits on a queued member, or
# conflicts.
cut_to_top() {
  local root=$1 stack=$2 flagged=$3 queued members=() member at=0 flag paths decision chain top status=0 heads=() numbers
  queued=$(queued_of "$stack")
  mapfile -t heads < <(jq -r '.[].head' <<< "$stack")
  git fetch --quiet origin "$trunk" "${heads[@]}"
  for member in $(jq -r '.[].number' <<< "$stack"); do
    flag=$(jq --argjson n "$member" 'index($n) != null' <<< "$flagged")
    paths=$(member_paths "$stack" "$at")
    members+=("$(jq -cn --argjson number "$member" --argjson red "$flag" --argjson queued "$queued" --argjson paths "$paths" \
      '{number: $number, red: $red, queued: ($number | IN($queued[])), paths: $paths}')")
    at=$((at + 1))
  done
  decision=$(jq -cn --argjson own "$(jq '.[-1].number' <<< "$stack")" '{heals: 0, own: $own, members: ($ARGS.positional | map(fromjson))}' --args "${members[@]}" \
    | jq -c -f "$pr_stack_dir/heal.jq")
  case $(jq -r .act <<< "$decision") in
    past) ;;
    wait)
      echo "the cut of #$root waits: $(jq -r '.queued | map("#\(.)") | join(" ")' <<< "$decision") in the merge queue never moves" >&2
      return 1
      ;;
    *)
      echo "the cut of #$root is refused: a member above it is red too, or changes a path #$root changes" >&2
      return 1
      ;;
  esac
  host_lock --fd 7 stack-cut 1 "cut #$root"
  restack_past "$stack" "$root" > /dev/null || status=$?
  if (( status == 0 )); then
    chain=$(jq -c --argjson root "$root" 'map(select(.number != $root))' <<< "$stack")
    top=$(jq -r '.[-1].head' <<< "$chain")
    set_base "$root" "$top" || status=$?
  fi
  if (( status == 0 )); then
    stack_link "$(jq -c --argjson stack "$stack" --argjson root "$root" '. + [$stack[] | select(.number == $root)]' <<< "$chain")" || status=$?
  fi
  if (( status == 0 )); then
    numbers=$(jq -c 'map(.number)' <<< "$stack")
    cancel_stale "$chain" "$numbers" || :
  fi
  host_unlock 7
  exec 7<&-
  (( status == 0 )) || return "$status"
  printf '%s\t%s\n' \
    "$(jq -r 'map("#\(.number)") | join(" ← ")' <<< "$stack")" \
    "$(jq -r --argjson root "$root" 'map(select(.number != $root) | "#\(.number)") + ["#\($root)"] | join(" ← ")' <<< "$stack")"
}

# Cancel the runs a cut made stale (#5073, `stale.jq`): a queued or running
# run of a moved branch of `$1` (`[{number, head}]`) at a head the branch no
# longer has, and a merge-group run of a group of a cut pull request among
# `$2` (numbers). Prints one line on stderr per run cancelled.
cancel_stale() {
  local heads runs id branch status
  heads=$(for branch in $(jq -r '.[].head' <<< "$1"); do
    jq -cn --arg branch "$branch" --arg sha "$(git rev-parse "origin/$branch")" '{($branch): $sha}'
  done | jq -cs 'add // {}')
  runs=$(for status in queued in_progress waiting requested pending; do
    gh api "repos/$repo/actions/runs?status=$status&per_page=100" --jq '.workflow_runs[] | {id, event, head_branch, head_sha, status}'
  done | jq -cs .) || return 1
  for id in $(jq -cn --slurpfile runs <(printf '%s\n' "$runs") --slurpfile heads <(printf '%s\n' "$heads") \
    --slurpfile numbers <(printf '%s\n' "$2") --arg trunk "$trunk" \
    '{runs: $runs[0], heads: $heads[0], numbers: $numbers[0], trunk: $trunk}' | jq -c -f "$pr_stack_dir/stale.jq" | jq -r '.[]'); do
    if gh api -X POST "repos/$repo/actions/runs/$id/cancel" > /dev/null 2>&1; then
      echo "cancelled the stale run $id" >&2
    fi
  done
}

# The reason of pull request `$1`'s last removal from the merge queue, in
# lower case, when nothing was queued or pushed since; empty otherwise. A
# removal for `failed_checks` is its own merge-group run failing (#3745).
queue_removal() {
  gh api graphql -F owner='{owner}' -F name='{repo}' -F number="$1" \
    -f query='query($owner: String!, $name: String!, $number: Int!) { repository(owner: $owner, name: $name) { pullRequest(number: $number) { timelineItems(last: 1, itemTypes: [ADDED_TO_MERGE_QUEUE_EVENT, REMOVED_FROM_MERGE_QUEUE_EVENT, HEAD_REF_FORCE_PUSHED_EVENT, PULL_REQUEST_COMMIT]) { nodes { __typename ... on RemovedFromMergeQueueEvent { reason } } } } } }' \
    --jq '.data.repository.pullRequest.timelineItems.nodes[0] | select(.__typename == "RemovedFromMergeQueueEvent") | .reason // "" | ascii_downcase'
}

# The paths the own commits of the member at index `$2` of the stack `$1`
# change, from its fork off the member below it, or off the trunk for the
# bottom, as a JSON array. The branches are fetched.
member_paths() {
  local below head
  head=$(jq -r ".[$2].head" <<< "$1")
  if (( $2 == 0 )); then below=$trunk; else below=$(jq -r ".[$2 - 1].head" <<< "$1"); fi
  git diff --no-renames --name-only "origin/$below...origin/$head" | jq -R . | jq -sc .
}

# The commit a restack replays the branch `$1` from (#3078): of the heads a
# pull request merged below it ever had (`landed_heads`), the newest the
# branch still contains, else `$2`, its merge base with the trunk. A lower
# pull request restacked after the branch was stacked on it lands commits the
# branch does not hold; the branch keeps the earlier ones, whose patch-ids
# differ wherever the restack resolved a conflict, so the trunk's merge base
# alone would replay them onto their own landing (#3047: two of #3041's and
# #3043's earlier commits above #3034's merge).
landed_fork() {
  local branch=$1 fork=$2 oid
  while read -r oid; do
    if git merge-base --is-ancestor "$oid" "origin/$branch" 2> /dev/null && git merge-base --is-ancestor "$fork" "$oid"; then
      fork=$oid
    fi
  done < <(landed_heads "$branch")
  printf '%s\n' "$fork"
}

# The commit a restack replays the branch at `$2` (a commit) from onto the
# open branch `$1` below it, when that branch was force-pushed after `$2`
# was stacked on it (#3115): of the server's tip of `$1` and every head its
# open pull request's force pushes replaced or set (`pushed_heads`), the
# newest `$2` contains. Prints nothing when `$2` contains none.
relink_fork() {
  local below=$1 commit=$2 oid held=
  while read -r oid; do
    if git merge-base --is-ancestor "$oid" "$commit" 2> /dev/null \
      && { [[ -z $held ]] || git merge-base --is-ancestor "$held" "$oid"; }; then
      held=$oid
    fi
  done < <(git rev-parse "origin/$below"; pushed_heads "$below" OPEN)
  [[ -z $held ]] || printf '%s\n' "$held"
}

# Every head a merged pull request below the open pull request of branch `$1`
# ever had, one commit id a line: the branches its base was moved off (GitHub
# retargets it when the base's pull request merges, or a hand does), and for
# each the merged pull request's `pushed_heads`.
landed_heads() {
  local branch=$1 base
  for base in $(gh api graphql -F owner='{owner}' -F name='{repo}' -F head="$branch" -f query='
    query($owner: String!, $name: String!, $head: String!) {
      repository(owner: $owner, name: $name) {
        pullRequests(headRefName: $head, states: OPEN, first: 1) {
          nodes { timelineItems(last: 20, itemTypes: [AUTOMATIC_BASE_CHANGE_SUCCEEDED_EVENT, BASE_REF_CHANGED_EVENT]) {
            nodes { ... on AutomaticBaseChangeSucceededEvent { oldBase } ... on BaseRefChangedEvent { previousRefName } } } }
        }
      }
    }' --jq '[.data.repository.pullRequests.nodes[].timelineItems.nodes[] | (.oldBase // .previousRefName) | values] | unique[]'); do
    [[ $base != "$trunk" ]] || continue
    pushed_heads "$base" MERGED
  done
}

# The heads the pull requests of branch `$1` in state `$2` (`OPEN` or
# `MERGED`) had, one commit id a line: each one's last head and every head a
# force push replaced or set.
pushed_heads() {
  gh api graphql -F owner='{owner}' -F name='{repo}' -F head="$1" -F state="$2" -f query='
    query($owner: String!, $name: String!, $head: String!, $state: PullRequestState!) {
      repository(owner: $owner, name: $name) {
        pullRequests(headRefName: $head, states: [$state], last: 5) {
          nodes { headRefOid timelineItems(first: 100, itemTypes: [HEAD_REF_FORCE_PUSHED_EVENT]) {
            nodes { ... on HeadRefForcePushedEvent { beforeCommit { oid } afterCommit { oid } } } } }
        }
      }
    }' --jq '.data.repository.pullRequests.nodes[] | .headRefOid, (.timelineItems.nodes[] | .beforeCommit.oid, .afterCommit.oid) | values'
}

# The scratch worktree `restack` made, removed; a no-op when there is none.
# `pr:land` and `pr:watch` run it on every exit.
pr_stack_scratch=
drop_scratch() {
  [[ -n "$pr_stack_scratch" ]] || return 0
  git worktree remove --force "$pr_stack_scratch" 2> /dev/null || rm -rf "$pr_stack_scratch"
  git worktree prune
  pr_stack_scratch=
}

# Move branch `$1` from head `$4` to the commits `$2..$3` of the local
# clone, as commits GitHub signs (#5214). The trunk's rules refuse an
# unsigned commit, a runner holds no signing key, and `update-branch`'s
# rebase writes unsigned commits (#3355). Each commit is replayed through
# `createCommitOnBranch`, with its message and its changed files, on a
# scratch branch `restack/<branch>` made at `$2`'s commit. GitHub signs each one.
# The mutation takes no file mode: a file a commit adds comes out `100644`.
# So the branch moves only when the replay's tree is `$3`'s, and only while
# it still holds `$4`. The replay's tree is read from a fetch of the scratch
# head, and a replay with another tree is refused naming each path that
# differs (`replay_difference`, #6020). Prints the new head. Fails with the
# branch unmoved and the scratch deleted otherwise, naming why on stderr.
signed_replay() {
  local branch=$1 onto=$2 tip=$3 expect=$4 scratch head commit status path request now
  scratch=restack/$branch
  head=$(git rev-parse "$onto^{commit}")
  request=$(mktemp -d)
  gh api --method POST "repos/$repo/git/refs" -f ref="refs/heads/$scratch" -f sha="$head" > /dev/null || {
    echo "the scratch branch $scratch could not be made" >&2
    rm -rf "$request"
    return 1
  }
  for commit in $(git rev-list --reverse "$onto..$tip"); do
    printf '[]' > "$request/additions"
    printf '[]' > "$request/deletions"
    while IFS= read -r -d '' status && IFS= read -r -d '' path; do
      if [[ $status == D ]]; then
        jq -c --arg path "$path" '. + [{path: $path}]' "$request/deletions" > "$request/next" && mv "$request/next" "$request/deletions"
      else
        # `tr` joins GNU's 76-column lines; BSD's base64 has no `-w`.
        git show "$commit:$path" | base64 | tr -d '\n' > "$request/contents"
        jq -c --arg path "$path" --rawfile contents "$request/contents" '. + [{path: $path, contents: $contents}]' "$request/additions" > "$request/next" \
          && mv "$request/next" "$request/additions"
      fi
    done < <(git diff-tree --no-commit-id --no-renames -r -z --name-status "$commit^" "$commit")
    jq -n --arg repo "$repo" --arg branch "$scratch" --arg head "$head" \
      --rawfile headline <(printf '%s' "$(git log -1 --format=%s "$commit")") \
      --rawfile body <(printf '%s' "$(git log -1 --format=%b "$commit")") \
      --slurpfile additions "$request/additions" --slurpfile deletions "$request/deletions" \
      '{query: "mutation($input: CreateCommitOnBranchInput!) { createCommitOnBranch(input: $input) { commit { oid } } }",
        variables: {input: {branch: {repositoryNameWithOwner: $repo, branchName: $branch}, expectedHeadOid: $head,
          message: {headline: $headline, body: $body},
          fileChanges: {additions: $additions[0], deletions: $deletions[0]}}}}' > "$request/body"
    if ! head=$(gh api graphql --input "$request/body" --jq .data.createCommitOnBranch.commit.oid) || [[ -z $head ]]; then
      echo "the signed replay of $(git log -1 --format='%h %s' "$commit") onto $scratch failed" >&2
      gh api --method DELETE "repos/$repo/git/refs/heads/$scratch" > /dev/null 2>&1 || :
      rm -rf "$request"
      return 1
    fi
  done
  rm -rf "$request"
  if ! git fetch --quiet origin "+refs/heads/$scratch:refs/restack/$branch"; then
    echo "the fetch of the signed replay $scratch failed" >&2
    gh api --method DELETE "repos/$repo/git/refs/heads/$scratch" > /dev/null 2>&1 || :
    return 1
  fi
  if [[ $(git rev-parse "refs/restack/$branch^{tree}") != $(git rev-parse "$tip^{tree}") ]]; then
    replay_difference "$branch" "$tip" "refs/restack/$branch" >&2
    git update-ref -d "refs/restack/$branch"
    gh api --method DELETE "repos/$repo/git/refs/heads/$scratch" > /dev/null 2>&1 || :
    return 1
  fi
  git update-ref -d "refs/restack/$branch"
  now=$(gh api "repos/$repo/git/ref/heads/$branch" --jq .object.sha) || now=
  if [[ $now != "$expect" ]]; then
    echo "$branch moved to ${now:-nothing} while it was replayed; nothing is pushed" >&2
    gh api --method DELETE "repos/$repo/git/refs/heads/$scratch" > /dev/null 2>&1 || :
    return 1
  fi
  if ! gh api --method PATCH "repos/$repo/git/refs/heads/$branch" -f sha="$head" -F force=true > /dev/null; then
    echo "the move of $branch to its signed replay failed" >&2
    gh api --method DELETE "repos/$repo/git/refs/heads/$scratch" > /dev/null 2>&1 || :
    return 1
  fi
  gh api --method DELETE "repos/$repo/git/refs/heads/$scratch" > /dev/null 2>&1 || :
  echo "$head"
}

# Why the signed replay `$3` of branch `$1` gives another tree than the
# rebase's tip `$2` (#6020): one line for each path that differs, with its
# mode and its blob on each side, `000000` and a zero blob where a side holds
# no file. Only when every path differs in its mode alone does the first
# line name that cause, as `createCommitOnBranch` takes no mode.
replay_difference() {
  local branch=$1 tip=$2 replay=$3 rows reason=": a file it adds keeps no mode"
  # awk exits 1 when a blob differs, so the cause is not the mode alone.
  if ! rows=$(git diff-tree -r --no-renames "$tip" "$replay" | awk -F '\t' '{
    split(substr($1, 2), side, " ")
    if (side[3] != side[4]) blobs = 1
    printf "  %s: %s %s in the rebase, %s %s in the replay\n", $2, side[1], substr(side[3], 1, 12), side[2], substr(side[4], 1, 12)
  } END { exit blobs }'); then
    reason=" at these paths"
  fi
  echo "the signed replay of $branch gives another tree than the rebase$reason"
  printf '%s\n' "$rows"
}

# Rebase branch `$1`, at head `$2`, onto its base `$3` in a scratch worktree,
# and move the branch there as signed commits: `chain_replay` with the
# `github` signer, the branch alone (#5749). The replay starts from
# `origin/$3`, so the rebase is `git rebase origin/$3`: it drops a commit
# whose change the base already carries (#4463), where GitHub's rebase
# replays it empty. A branch that moved past `$2` since the caller read it
# is refused, as the replay would move a head that no reading decided on.
# Prints the new head, or nothing when the head already stands on the base.
# Fails, naming why on stderr, at a conflict or a refused replay.
signed_restack() {
  local branch=$1 oid=$2 base=$3 dir head old new status=0
  git fetch --quiet origin "$base" "$branch" || { echo "the fetch of $branch and $base failed" >&2; return 1; }
  if [[ $(git rev-parse "origin/$branch") != "$oid" ]]; then
    echo "$branch moved past ${oid::12} since it was read; nothing is replayed" >&2
    return 1
  fi
  dir=$(mktemp -d)
  git worktree add --quiet --detach "$dir" "$oid" || { rm -rf "$dir"; echo "the scratch worktree for $branch failed" >&2; return 1; }
  if chain_replay "$dir" "origin/$base" "origin/$base" github "$branch"; then
    read -r head old new <<< "${chain_moved[0]}"
    [[ $new == "$old" ]] || echo "$new"
  else
    [[ -z $chain_files ]] || echo "the rebase of $branch onto $base conflicts: $chain_files" >&2
    status=1
  fi
  git worktree remove --force "$dir" 2> /dev/null || rm -rf "$dir"
  git worktree prune
  return "$status"
}

# Remove this clone's worktree of pull request `$1`'s branch once it merged,
# in the foreground: `wt remove` deletes the branch as merged and refuses a
# dirty or otherwise unsafe tree, whose refusal is printed and the tree kept.
# The primary worktree is never removed. Prints on stderr only.
#
# `pr:land` and `pr:watch` both run this, usually from the branch's own
# worktree, so whichever sees the merge second finds its working directory
# gone, and every later git command fails ("Unable to read current working
# directory"). The function therefore first moves the shell to the primary
# worktree, read when this file is sourced; the caller exits right after.
pr_stack_primary=$(git worktree list --porcelain | sed -n '1s/^worktree //p')
remove_landed_worktree() {
  local branch path out
  cd "$pr_stack_primary" || return 0
  branch=$(gh pr view "$1" -R "$repo" --json headRefName --jq .headRefName) || return 0
  path=$(git worktree list --porcelain | awk -v ref="branch refs/heads/$branch" '/^worktree / { tree = substr($0, 10) } $0 == ref { print tree }')
  [[ -n "$path" && "$path" != "$pr_stack_primary" ]] || return 0
  if out=$(wt remove --foreground --yes "$path" 2>&1); then
    echo "removed the worktree of #$1 at $path" >&2
  else
    echo "kept the worktree of #$1 at $path: ${out##*$'\n'}" >&2
  fi
}

# The trunk's required status contexts, from its rules, as a JSON array.
required_contexts() {
  gh api "repos/$repo/rules/branches/$trunk" \
    --jq '[.[] | select(.type == "required_status_checks") | .parameters.required_status_checks[].context] | unique'
}

# The most members one landing queues of a stack (#2046): the trunk's
# merge-queue `max_entries_to_merge`, a zero read as no bound. A stack up to
# that size fits one merge group, which the queue builds and merges whole, so
# `max_entries_to_build` bounds nothing here. `landing` builds one group of up
# to 10 (#5438), and the smaller of the two would queue one member at a time.
queue_unit_cap() {
  gh api "repos/$repo/rules/branches/$trunk" \
    --jq '[.[] | select(.type == "merge_queue") | .parameters.max_entries_to_merge | select(. > 0)] | min // 0'
}

# Wait, every 30 seconds, until each of the trunk's required contexts on pull
# request `$1`'s head has concluded (`required.jq`, #1601); fail at the first
# reading with a required context red, naming it. The contexts are read from
# the rules, not through `gh pr checks --required`, so the wait never rests
# on gh's filter nor on the end of a run whose other jobs are not required.
wait_required() {
  local required reading
  required=$(required_contexts)
  while :; do
    reading=$(required_reading "$1" "$required")
    if [[ $(jq '.failed | length' <<< "$reading") != 0 ]]; then
      echo "#$1's required checks are red: $(jq -r '.failed | join(", ")' <<< "$reading")" >&2
      return 1
    fi
    [[ $(jq '.pending | length' <<< "$reading") != 0 ]] || return 0
    sleep 30
  done
}

# Re-run the jobs that a twin on the same commit cancelled in the runs on pull
# request `$1`'s head (`twins.jq`); succeeds when it re-ran one. `--failed`
# re-runs a run's cancelled and failed jobs with their dependents, and keeps
# each job that passed: the twin cancels a run part of the way (#2911).
rerun_twins() {
  local sha ids id
  sha=$(pr_reading "$1" | jq -r .headRefOid)
  mapfile -t ids < <(gh run list -R "$repo" --commit "$sha" --event pull_request --limit 100 \
    --json databaseId,workflowName,startedAt,conclusion | jq -c -f "$pr_stack_dir/twins.jq" | jq -r '.[]')
  for id in "${ids[@]}"; do
    echo "#$1: re-running the cancelled jobs of run $id, cancelled by its twin on ${sha::12}" >&2
    gh run rerun "$id" --failed -R "$repo"
  done
  (( ${#ids[@]} > 0 ))
}

# The open pull requests whose commits the branch `$2` holds past the base
# `$3` (`foreign.jq`, #6797), as a JSON array, empty when the base agrees
# with the branch. `$1` is the unit's pull request, or `null` before it
# opens. `$4` is the head read in place of `origin/$2`, such as a replay not
# yet pushed or a branch not yet pushed. One fetch takes every open head, and
# each commit list reaches jq on its standard input, never as an argument
# (#6374).
foreign_commits() {
  local number=$1 head=$2 base=$3 tip=${4:-} open other ohead above heads=()
  open=$(open_prs) || return 1
  mapfile -t heads < <(jq -r --arg head "$head" '.[] | select(.head != $head) | .head' <<< "$open")
  if [[ -z $tip ]]; then
    heads+=("$head")
    tip=origin/$head
  fi
  git fetch --quiet origin "$base" "${heads[@]}" || return 1
  {
    git rev-list "origin/$base..$tip" | jq -Rsc --argjson number "$number" '{own: true, number: $number, commits: (split("\n") | map(select(. != "")))}'
    while IFS=$'\t' read -r other ohead; do
      above=false
      if git merge-base --is-ancestor "$tip" "origin/$ohead"; then above=true; fi
      git rev-list "origin/$base..origin/$ohead" \
        | jq -Rsc --argjson number "$other" --argjson above "$above" '{own: false, number: $number, above: $above, commits: (split("\n") | map(select(. != "")))}'
    done < <(jq -r --arg head "$head" '.[] | select(.head != $head) | [.number, .head] | @tsv' <<< "$open")
  } | jq -sc '(map(select(.own)) | first) as $own | {number: $own.number, commits: $own.commits, open: map(select(.own | not) | del(.own))}' \
    | jq -c -f "$pr_stack_dir/foreign.jq"
}

# Set pull request `$1`'s base to `$2` only while its branch, or the head
# `$3` read in its place, holds no commit of another open pull request past
# `$2` (`foreign_commits`, #6797): a landing over that base would squash
# those commits under its title. A refusal names them on stderr, changes
# nothing and returns 1.
set_base() {
  local number=$1 base=$2 tip=${3:-} head foreign
  head=$(open_prs | jq -r --argjson n "$number" '.[] | select(.number == $n) | .head')
  [[ -n $head ]] || { echo "#$number is not open, so its base stays" >&2; return 1; }
  foreign=$(foreign_commits "$number" "$head" "$base" "$tip") \
    || { echo "the commits of #$number past $base cannot be read, so its base stays" >&2; return 1; }
  if [[ $foreign != '[]' ]]; then
    echo "#$number keeps its base: past $base its branch holds $(jq -r 'map("\(.commits) commit(s) of #\(.number)") | join(", ")' <<< "$foreign"), which a landing over $base would squash under its title (#6797)" >&2
    return 1
  fi
  gh pr edit "$number" -R "$repo" --base "$base" > /dev/null
}

# Retarget to the trunk every open pull request the landing of `$1`, a JSON
# array of pull request numbers, would close (`retarget.jq`, #1420): GitHub
# deletes a merged branch and closes, unmerged, every open pull request still
# based on it that no linked stack carries. Each survives on the trunk, and
# `pr:land` from its top rebases it. A pull request whose branch holds the
# commits of a pull request still open keeps its base (`set_base`, #6797):
# on the trunk, a landing would squash those commits under its title. Prints
# one line on stderr for each.
retarget_landing() {
  local number base
  while IFS=$'\t' read -r number base; do
    [[ -n "$number" ]] || continue
    set_base "$number" "$trunk" || continue
    echo "#$number retargeted from $base to $trunk: the landing deletes its base" >&2
  done < <(open_prs | jq -r --argjson landing "$1" -f "$pr_stack_dir/retarget.jq" | jq -r '.[] | [.number, .base] | @tsv')
}

# The pull requests a waiting `pr:land` holds, labelled `landing` (#1556):
# from the moment it starts waiting until the chain is queued, the top is not
# in the merge queue yet, so without the label a `pr:open` would stack on it
# and move the top out from under the landing. `hold_landing` labels each of
# the JSON array `$1`'s pull requests and remembers them; `release_landing`
# takes the label off every one it holds, and `pr:land` runs it when the chain
# is queued and on every exit, a refusal or a red check included. A label a
# killed seat left behind is taken off by `pr:watch` once its pull request is
# queued or merged.
landing_held=()
hold_landing() {
  local number
  for number in $(jq -r '.[]' <<< "$1"); do
    [[ " ${landing_held[*]} " == *" $number "* ]] && continue
    gh pr edit "$number" -R "$repo" --add-label landing > /dev/null
    landing_held+=("$number")
  done
}
release_landing() {
  local number
  for number in "${landing_held[@]}"; do
    gh pr edit "$number" -R "$repo" --remove-label landing > /dev/null 2>&1 || true
  done
  landing_held=()
}

# The open pull requests outside the stack `$1` that are in the merge queue,
# or set to enter it, and whose branch the stack's top holds, as a JSON array
# of numbers. A pull request retargeted off a branch that lands on its own
# (`retarget_landing`) still carries that branch's commits, so its stack
# lands only once they have merged. One queued off the trunk, on a base no
# open pull request heads, never merges, so the stack lands past it, and it
# is named on stderr (`carried.jq`, #4168).
carried_queued() {
  local top number head held=() open carried
  top=$(jq -r '.[-1].head' <<< "$1")
  git fetch --quiet origin "$top"
  open=$(open_prs)
  while IFS=$'\t' read -r number head; do
    [[ -n "$number" && $(in_queue "$number") == true ]] || continue
    git fetch --quiet origin "$head" || continue
    if git merge-base --is-ancestor "origin/$head" "origin/$top"; then held+=("$number"); fi
  done < <(jq -r --argjson stack "$1" '.[] | select(.number | IN($stack[].number) | not) | [.number, .head] | @tsv' <<< "$open")
  carried=$(jq -cn --argjson open "$open" --arg trunk "$trunk" '{open: $open, trunk: $trunk, held: ($ARGS.positional | map(tonumber))}' --args "${held[@]}" \
    | jq -c -f "$pr_stack_dir/carried.jq")
  jq -r '.off[] | "queued-off-trunk #\(.number) on \(.base): its queue merges nothing into the trunk, so the stack lands past it"' <<< "$carried" >&2
  jq -c .wait <<< "$carried"
}

# The newest pull request, closed or merged, whose head is branch `$1`, as
# `{number, head, base, oid}` when it closed unmerged (#5695); `null` when it
# merged, or when no pull request has the branch as its head.
closed_pr() {
  gh api graphql -F owner='{owner}' -F name='{repo}' -f head="$1" \
    -f query='query($owner: String!, $name: String!, $head: String!) { repository(owner: $owner, name: $name) { pullRequests(headRefName: $head, states: [CLOSED, MERGED], last: 1) { nodes { number state headRefName baseRefName headRefOid } } } }' \
    --jq '.data.repository.pullRequests.nodes[0] // null | if . != null and .state == "CLOSED" then {number, head: .headRefName, base: .baseRefName, oid: .headRefOid} else null end'
}

# Unstack the chain `$3` and retarget its bottom, pull request `$1`, onto `$2`,
# the base of the member closed unmerged below it (#6176). GitHub refuses a
# stacked member's base change. The base changes before any member moves, so
# GitHub reads each push against the base it lands on: a push onto a base it
# conflicts with starts no `CI` run, and a base change starts none either. A
# failed base change links the chain again and names it on stderr.
base_closed() {
  local stack
  stack=$(stack_of "$1")
  [[ $stack == null ]] || gh stack unstack "$stack" < /dev/null > /dev/null 2>&1 || :
  set_base "$1" "$2" && return 0
  stack_link "$3" || :
  echo "the base of #$1 did not change to $2, so the cut past the member closed below it moved nothing" >&2
  return 1
}

# Cut the pull request `$1` (`closed_pr`), closed unmerged, out from under
# the chain `$2` stacked on it, bottom to top (#5695), as `cut_bottom` cuts a
# red one. Each member's own commits, those past the old head below it, are
# replayed onto the new head below it, and the bottom's onto the closed one's
# base (`chain_replay`). So the closed one's commits are left out. GitHub
# signs each replayed commit (`signed_replay`), because a runner holds no
# signing key. The cut is refused with nothing moved when a member is queued
# (#2531), or when a member above the bottom does not hold the head below it
# (`chain_gap`). Before any member moves, the bottom stands on the closed
# one's base (`base_closed`, #6176). After the replays, the moved members are
# linked again (`stack_link`). A conflict or a refused replay stops the cut
# and names the member. The members below it stay moved and linked. A bottom
# that does not move, or that does not hold the closed one's head, stands on
# the new base with the closed one's commits. So it is held as a draft
# (`pr:hold`), and its seat rebases it by hand onto that base and releases it
# (`pr:release`). Its push then starts `CI`. Prints one line on stderr.
cut_closed() {
  local closed=$1 chain=$2 number base below dir gap moved status=0 heads=() numbers=()
  IFS=$'\t' read -r number base below < <(jq -r '[.number, .base, .oid] | @tsv' <<< "$closed")
  mapfile -t heads < <(jq -r '.[].head' <<< "$chain")
  mapfile -t numbers < <(jq -r '.[].number' <<< "$chain")
  if [[ $(queued_of "$chain") != '[]' ]]; then
    echo "the cut past #$number, closed unmerged, waits: a member of the chain over it is queued, and a queued branch never moves" >&2
    return 1
  fi
  git fetch --quiet origin "$base" "${heads[@]}" "refs/pull/$number/head" || { echo "the fetch of the chain over #$number failed" >&2; return 1; }
  if ! gap=$(chain_gap "$below" "${heads[@]}"); then
    if (( gap > 0 )); then
      echo "the cut past #$number is refused: ${heads[gap]} does not hold ${heads[gap-1]}, the branch below it; rebase it onto ${heads[gap-1]} first" >&2
    elif base_closed "${numbers[0]}" "$base" "$chain"; then
      gh pr ready "${numbers[0]}" -R "$repo" --undo > /dev/null || :
      echo "the cut past #$number is refused: ${heads[0]} does not hold the head of #$number, which moved after the chain stacked on it; #${numbers[0]} stands on $base as a draft: rebase ${heads[0]} onto $base without the commits of #$number, then \`mise run pr:release ${numbers[0]}\`" >&2
    fi
    return 1
  fi
  dir=$(mktemp -d)
  git worktree add --quiet --detach "$dir" "origin/${heads[0]}" || { rm -rf "$dir"; echo "the scratch worktree for the cut past #$number failed" >&2; return 1; }
  if ! base_closed "${numbers[0]}" "$base" "$chain"; then
    git worktree remove --force "$dir" 2> /dev/null || rm -rf "$dir"
    git worktree prune
    return 1
  fi
  if ! chain_replay "$dir" "origin/$base" "$below" github "${heads[@]}"; then
    [[ -z $chain_files ]] || echo "the cut of #${numbers[chain_stop]} past #$number onto $base conflicts ($chain_files): rebase it by hand" >&2
    status=1
  fi
  moved=${#chain_moved[@]}
  git worktree remove --force "$dir" 2> /dev/null || rm -rf "$dir"
  git worktree prune
  if (( moved > 0 )); then
    stack_link "$(jq -c --argjson moved "$moved" '.[: $moved]' <<< "$chain")" || status=1
  else
    gh pr ready "${numbers[0]}" -R "$repo" --undo > /dev/null || :
    echo "#${numbers[0]} stands on $base as a draft with the commits of #$number: rebase it onto $base by hand, then \`mise run pr:release ${numbers[0]}\`" >&2
  fi
  (( status == 0 )) || return "$status"
  echo "#${numbers[0]} cut past #$number, closed unmerged: $(jq -r 'map("#\(.number)") | join(" ← ")' <<< "$chain") replayed onto $base without its commits" >&2
}

# Replay the stack `$1` (bottom to top, `{number, head}`), whose bottom
# stands on an old lineage of the trunk (#6399), onto `origin/$trunk` before
# anything of it is queued. The landing rebase and the integration cycle
# rewrite `landing`, and the merge queue refuses a head that still carries the
# old commits. `$2` is the fork that `rewritten_fork` reads for the bottom,
# and `$3` the count of the commits it holds by patch. Each member's own
# commits replay as `chain_replay` replays them: the bottom's from the fork,
# each upper's from the old tip below it. The replay runs on the `github`
# signer, as `cut_closed` runs it, so a runner without a signing key replays
# the same way. The new heads start their checks, and the stack lands from
# them once they pass. Returns 3 after the replay, with one line on stderr.
# Returns 2 at a conflict or a refused replay, naming the member and the
# command that replays it by hand. The members below the stop stay replayed.
replay_lineage() {
  local stack=$1 fork=$2 held=$3 dir status=0 heads=() numbers=()
  mapfile -t heads < <(jq -r '.[].head' <<< "$stack")
  mapfile -t numbers < <(jq -r '.[].number' <<< "$stack")
  git fetch --quiet origin "${heads[@]}" || { echo "the fetch of the stack over #${numbers[0]} failed" >&2; return 2; }
  dir=$(mktemp -d)
  git worktree add --quiet --detach "$dir" "origin/${heads[0]}" || { rm -rf "$dir"; echo "the scratch worktree for the replay of #${numbers[0]} failed" >&2; return 2; }
  if ! chain_replay "$dir" "origin/$trunk" "$fork" github "${heads[@]}"; then
    if [[ -n $chain_files ]] && (( chain_stop == 0 )); then
      echo "the replay of #${numbers[0]} off an old lineage of $trunk conflicts ($chain_files): replay it by hand with \`git rebase --onto origin/$trunk ${fork:0:12}\`, push, then land again" >&2
    elif [[ -n $chain_files ]]; then
      echo "the replay of #${numbers[chain_stop]} onto ${heads[chain_stop-1]} conflicts ($chain_files): rebase it onto ${heads[chain_stop-1]} by hand, push, then land again" >&2
    fi
    status=2
  fi
  git worktree remove --force "$dir" 2> /dev/null || rm -rf "$dir"
  git worktree prune
  (( status == 0 )) || return "$status"
  echo "#${numbers[0]} stood on an old lineage of $trunk, with $held commit(s) that $trunk holds under other hashes: $(jq -r 'map("#\(.number)") | join(" ← ")' <<< "$stack") replayed onto $trunk, and the stack lands once the new heads' checks pass" >&2
  return 3
}

# Bring the stack bottom `$1`, standing off the trunk as `bottom.jq` reads it
# (#4168), back to a base that lands; `$2` is its chain, bottom to top. A base
# that a pull request closed unmerged heads, or headed before its branch was
# deleted, is cut out from under the chain (`cut_closed`, #5695). A base that
# merged or is gone is retargeted to the trunk. A queued bottom leaves the
# queue first by being closed and reopened, the only way out of a queue on a
# base other than the trunk, and a bottom a server stack holds is unstacked,
# since GitHub refuses a stacked member's base change (#1520). A base that
# still stands unmerged and heads no closed pull request is refused by name,
# returning 2, and so is a cut that fails. Prints one line on stderr.
retarget_bottom() {
  local number base stack closed=null
  IFS=$'\t' read -r number base stack < <(jq -r '[.number, .base, (.stack // "")] | @tsv' <<< "$1")
  if git ls-remote --exit-code --heads origin "$base" > /dev/null; then
    git fetch --quiet origin "$trunk" "$base"
    if ! git merge-base --is-ancestor "origin/$base" "origin/$trunk"; then
      closed=$(closed_pr "$base") || closed=null
      if [[ $closed == null ]]; then
        echo "#$number stands on $base, which is not $trunk, heads no open pull request and has not merged: rebase it onto the pull request it builds on, or onto $trunk" >&2
        return 2
      fi
    fi
  else
    closed=$(closed_pr "$base") || closed=null
  fi
  if [[ $closed != null ]]; then
    cut_closed "$closed" "$2" || return 2
    return 0
  fi
  if [[ $(jq -r .landing <<< "$1") == true ]]; then
    gh pr close "$number" -R "$repo" > /dev/null
    gh pr reopen "$number" -R "$repo" > /dev/null
  fi
  if [[ -n "$stack" ]]; then gh stack unstack "$stack" < /dev/null > /dev/null 2>&1 || :; fi
  set_base "$number" "$trunk" || return 2
  echo "#$number retargeted from $base to $trunk: its base merged or is gone, and no landing reaches $trunk from it" >&2
}

# Queue the stack `$1`, bottom to top, up to and including pull request `$3`
# (#1988), past the members of the JSON array `$2` already in the merge
# queue. A stack of one is a plain landing, queued by auto-merge, unless it
# still belongs to a server stack whose members below it merged: GitHub
# refuses auto-merge for a stacked pull request, so it is queued by the
# stack merge, unlinked. A longer stack is linked on the server, only its
# open members when part of it is queued, and queued by GitHub's stack merge,
# which takes every member up to and including `$3` atomically. Every open
# pull request on a branch the landing deletes, outside it, is retargeted to
# the trunk first (`retarget_landing`). The stack merge refuses a pull
# request whose required checks are still expected, so each queued member's
# are waited on (`wait_required`), and a red one stops the landing, naming
# it. A cancelled run the rollup reads, left by a restack's twin runs, is
# re-run (`rerun_twins`), at most three times for a pull request. Returns 3
# when the open members take no link above the queued ones: GitHub refuses
# one over a pull request queued on its own, and a single open member in no
# server stack takes none, so the stack merge would not know `$3` (#4843).
# The stack is read again once the queued ones merge.
queue_stack() {
  local stack=$1 queued=$2 upto=$3 open landing number reruns watched bottom foreign
  open=$(jq -c --argjson queued "$queued" '[.[] | select(.number | IN($queued[]) | not)]' <<< "$stack")
  mapfile -t landing < <(jq -r --argjson upto "$upto" '(map(.number) | index($upto)) as $end | .[: $end + 1][].number' <<< "$open")
  # The lowest open member lands over the member queued below it, or over the
  # trunk, so a commit of another open pull request on its branch past that
  # base would merge under its title (#6797): the stack waits for that pull
  # request, or for a restack.
  bottom=$(jq -c --argjson stack "$stack" --arg trunk "$trunk" '.[0] as $low | ($stack | map(.number) | index($low.number)) as $at | $low + {base: (if $at > 0 then $stack[$at - 1].head else $trunk end)}' <<< "$open")
  foreign=$(foreign_commits "$(jq -r .number <<< "$bottom")" "$(jq -r .head <<< "$bottom")" "$(jq -r .base <<< "$bottom")") || return 1
  if [[ $foreign != '[]' ]]; then
    echo "the stack is not queued: past $(jq -r .base <<< "$bottom"), the branch of its lowest open member #$(jq -r .number <<< "$bottom") holds $(jq -r 'map("\(.commits) commit(s) of #\(.number)") | join(", ")' <<< "$foreign"); restack it onto the pull request it builds on, then land again (#6797)" >&2
    return 1
  fi
  retarget_landing "$(jq -cn '$ARGS.positional | map(tonumber)' --args "${landing[@]}")"
  if [[ $(jq length <<< "$stack") == 1 ]]; then
    if [[ $(stack_of "$upto") == null ]]; then
      gh pr merge "$upto" -R "$repo" --merge --auto
      return
    fi
  elif [[ "$queued" == '[]' ]]; then
    stack_link "$stack"
  elif ! stack_link "$open" 2> /dev/null || [[ $(stack_of "$upto") == null ]]; then
    echo "the open pull requests above the queued #$(jq -r '.[-1]' <<< "$queued") take no link; they land once it merges" >&2
    return 3
  fi
  for number in "${landing[@]}"; do
    reruns=0
    while :; do
      watched=0
      wait_required "$number" || watched=$?
      if (( reruns < 3 )) && rerun_twins "$number"; then
        reruns=$(( reruns + 1 ))
        sleep 30
        continue
      fi
      if (( watched != 0 )); then
        echo "#$number's required checks failed; fix it, then land the stack again" >&2
        return 1
      fi
      break
    done
  done
  gh stack merge "$upto" --yes --merge
}

# Pull request `$1`'s head read against the trunk's required contexts `$2`
# (`required.jq`), from its reading `$3` or a fresh one. A head the CI depth
# gate stopped (#5074) reads its cancelled checks as pending: they wait for
# its promotion. The gate's mark is read only when a context failed.
required_reading() {
  local view=${3:-} reading
  [[ -n $view ]] || view=$(pr_reading "$1") || return 1
  reading=$(rollup_of <<< "$view" | jq -c --argjson required "$2" -f "$pr_stack_dir/required.jq")
  if [[ $(jq '.failed | length' <<< "$reading") != 0 ]] && depth_marked "$1" "$(jq -r .headRefOid <<< "$view")"; then
    reading=$(rollup_of <<< "$view" | jq -c --argjson required "$2" --argjson gated true -f "$pr_stack_dir/required.jq")
  fi
  printf '%s\n' "$reading"
}

# Pull request `$1`'s head read against the trunk's required contexts `$2`
# (`required_reading`) and its mergeability (`state.jq`, #2783):
# `conflicting` when it conflicts, else `green` when every context passed,
# `red` when one failed, `pending` otherwise.
required_state() {
  local view
  view=$(pr_reading "$1")
  required_reading "$1" "$2" "$view" \
    | jq -c --arg mergeable "$(jq -r .mergeable <<< "$view")" '. + {mergeable: $mergeable}' \
    | jq -r -f "$pr_stack_dir/state.jq"
}

# Why stack member `$1`, in state `$2` (`state.jq`), cuts the prefix below
# it: the words the landing prints after its number.
cut_reason() {
  case "$2" in
    conflicting) echo "#$1 conflicts with $trunk: rebase it" ;;
    red) echo "#$1's required checks are red" ;;
    *) echo "#$1's required checks are $2" ;;
  esac
}

# Queue the largest ready prefix of pull request `$1`'s stack (`prefix.jq`,
# #1988), at most `queue_unit_cap` members (#2046). The members outside the
# queue are read bottom up, and every one green on the trunk's required
# contexts and free of conflicts is queued, up to the first red, pending or
# conflicting one (#2783), which is named with what cuts it and where the
# reading stops, or up to the cap. A queued unit below the cap is
# topped up the same way to the cap (#2096); one at the cap takes nothing
# more. The tail above it is the next stack, landed the moment its own bottom
# goes green. `pr:land` runs this from any member, and `pr:watch` the moment
# its pull request goes green. Prints one line on stderr, and leaves its
# reading in `prefix_decision` (`prefix.jq`'s line), `prefix_server` (the
# stack) and `prefix_queued` (its queued members). Returns 0 when it queued
# the rest of the ready prefix or nothing was ready; 3 while a pull request
# queued on its own carries the stack's commits (`carried_queued`), while a
# queued unit takes nothing more, after queueing a unit the cap cut short,
# or when the open members take no link above the queued ones;
# `queue_stack`'s failure otherwise. A pull request held on purpose, or
# stacked above one, is refused with 2 and one line naming the hold
# (`rests.jq`, #3253): nothing of it is queued. Before the queue is read, a
# bottom standing off the trunk (`bottom.jq`, #4168) is brought back to it
# (`retarget_bottom`): retargeted, or cut past a member closed unmerged below
# it (#5695). Otherwise it is refused with 2 naming its base. A stack with
# nothing queued whose bottom stands on an old lineage of the trunk
# (`rewritten_fork`, #6399) is replayed onto the trunk and queued nothing
# (`replay_lineage`): 3 after the replay, 2 at a conflict.
land_prefix() {
  local server queued carried required cap room number state states=() decision verdict upto stop status=0 rests off lineage
  rests=$(open_prs | jq -c --argjson n "$1" --arg trunk "$trunk" -f "$pr_stack_dir/rests.jq")
  if [[ "$rests" != null ]]; then
    case $(jq -r .hold <<< "$rests") in
      owner) echo "#$(jq -r .number <<< "$rests") held by the owner; the stack above it waits: \`pr:release\` ends the hold" >&2 ;;
      *) echo "#$(jq -r .number <<< "$rests") is a draft, held on purpose; the stack above it waits: \`pr:release\` ends the hold" >&2 ;;
    esac
    return 2
  fi
  server=$(server_stack "$1")
  [[ $(jq length <<< "$server") != 0 ]] || { echo "PR #$1 is not open" >&2; return 2; }
  off=$(open_prs | jq -c --argjson n "$(jq '.[0].number' <<< "$server")" --arg trunk "$trunk" -f "$pr_stack_dir/bottom.jq")
  if [[ "$off" != null ]]; then
    retarget_bottom "$off" "$server" || return 2
    server=$(server_stack "$1")
  fi
  queued=$(queued_of "$server")
  if [[ "$queued" == '[]' ]]; then
    git fetch --quiet origin "$(jq -r '.[0].head' <<< "$server")"
    lineage=$(rewritten_fork "origin/$(jq -r '.[0].head' <<< "$server")")
    if [[ -n $lineage ]]; then
      replay_lineage "$server" "${lineage%%$'\t'*}" "${lineage#*$'\t'}" || status=$?
      return "$status"
    fi
  fi
  carried=$(carried_queued "$server")
  required=$(required_contexts)
  cap=$(queue_unit_cap)
  # A queued unit has the cap less its members left, none without a cap, and
  # a reading goes one member past the room.
  room=$cap
  if [[ "$queued" != '[]' ]]; then
    room=$(( cap > 0 ? cap - $(jq length <<< "$queued") : 0 ))
    (( room > 0 )) || room=-1
  fi
  for number in $(jq -r --argjson queued "$queued" '.[].number | select(IN($queued[]) | not)' <<< "$server"); do
    (( room < 0 || room > 0 && ${#states[@]} / 2 > room )) && break
    state=$(required_state "$number" "$required")
    states+=("$number" "$state")
    [[ "$state" == green ]] || break
  done
  decision=$(jq -rn --argjson server "$server" --argjson queued "$queued" --argjson carried "$carried" --argjson cap "$cap" \
    --argjson states "$(jq -cn '$ARGS.positional as $p | [range(0; $p | length; 2) | {key: $p[.], value: $p[. + 1]}] | from_entries' --args "${states[@]}")" \
    '{server: $server, queued: $queued, carried: $carried, states: $states, cap: $cap}' | jq -r -f "$pr_stack_dir/prefix.jq")
  prefix_decision=$decision prefix_server=$server prefix_queued=$queued
  verdict= upto= stop= state=
  IFS=$'\t' read -r verdict upto stop state <<< "$decision"
  case "$verdict" in
    wait)
      echo "#$upto, queued on its own, carries this stack's commits; the stack lands once it merges" >&2
      return 3
      ;;
    queued) echo "the stack is queued up to its top, #$(jq -r '.[-1].number' <<< "$server")" >&2 ;;
    busy)
      echo "#$upto is queued; the stack's next unit lands once it merges" >&2
      return 3
      ;;
    hold) echo "nothing lands: $(cut_reason "$upto" "$stop"), and the stack lands from it once it is ready" >&2 ;;
    land)
      hold_landing "$(jq -c --argjson queued "$queued" --argjson upto "$upto" \
        '[.[].number | select(IN($queued[]) | not)] | .[: index($upto) + 1]' <<< "$server")"
      queue_stack "$server" "$queued" "$upto" || status=$?
      release_landing
      (( status == 0 )) || return "$status"
      if [[ "$state" == capped ]]; then
        echo "queued the stack up to #$upto, a full unit; #$stop above it lands once the unit merges" >&2
        return 3
      fi
      echo "queued the stack up to #$upto${stop:+; above it, $(cut_reason "$stop" "$state"), and the stack lands from it once it is ready}" >&2
      ;;
    *) echo "unexpected landing decision: $decision" >&2; return 2 ;;
  esac
}
