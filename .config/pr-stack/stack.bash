# The stacking rule, mechanical (#1264), sourced by `pr:open`, `pr:land` and
# `pr:watch`. The server is the only record: every reading is of the open pull
# requests, and every stack is linked with `gh stack link`, which keeps no
# local state. Rebase order is the invariant: each branch sits on the one
# below it, and a restack moves the whole chain in one push.
#
# The caller sets `repo` (owner/name) and `trunk` (the default branch).

pr_stack_dir="$(git rev-parse --show-toplevel)/.config/pr-stack"

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

# The open pull requests that land, drafts left out, as a JSON array of
# `{number, head, base, created, landing, held, stack}`: `landing` when the
# pull request is in the merge queue or set to enter it (auto-merge), so its
# branch is about to be deleted and nothing new stacks on it (#1455); `held`
# when it carries the `landing` label, a `pr:land` waiting to queue it
# (#1556); `stack` the number of the linked stack holding it, or null (#1520).
open_prs() {
  gh api graphql --paginate -f owner="${repo%/*}" -f name="${repo#*/}" \
    -f query='query($owner: String!, $name: String!, $endCursor: String) { repository(owner: $owner, name: $name) { pullRequests(states: OPEN, first: 100, after: $endCursor) { pageInfo { hasNextPage endCursor } nodes { number headRefName baseRefName isDraft createdAt isInMergeQueue autoMergeRequest { enabledAt } labels(first: 50) { nodes { name } } stack { number } } } } }' \
    --jq '.data.repository.pullRequests.nodes[] | select(.isDraft | not) | {number, head: .headRefName, base: .baseRefName, created: .createdAt, landing: (.isInMergeQueue or .autoMergeRequest != null), held: any(.labels.nodes[]; .name == "landing"), stack: .stack.number}' \
    | jq -cs .
}

# The stack holding pull request `$1`, bottom to top (`chain.jq`).
server_stack() {
  open_prs | jq -c --argjson n "$1" --arg trunk "$trunk" -f "$pr_stack_dir/chain.jq"
}

# The open pull request a new one on branch `$1` stacks on (`top.jq`), or
# `null`.
stack_top() {
  open_prs | jq -c --arg own "$1" --arg trunk "$trunk" -f "$pr_stack_dir/top.jq"
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

# The commit below the checked-out branch `$1`'s own commits, where its rebase
# onto the top's branch `$2` starts (#1298). Its own commits are those above
# `origin/$trunk` that no other open pull request's head holds and whose patch
# `origin/$2` does not already carry. A branch an earlier run stacked holds
# the commits of the top it was stacked on, and of any pull request that top
# has since been rebased off; neither is its own. Its own commits sit at its
# top, so the parent of the oldest is the fork. Prints `HEAD` when it holds
# none.
own_fork() {
  local heads=() head commit
  local -A held=()
  for head in $(open_prs | jq -r --arg own "$1" '.[] | select(.head != $own) | .head'); do
    git fetch --quiet origin "$head"
    heads+=("origin/$head")
  done
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

# Whether pull request `$1` is in the merge queue or set to enter it on its
# own (auto-merge). Either way it lands alone, and GitHub refuses to link it
# into a stack.
in_queue() {
  gh api graphql -f owner="${repo%/*}" -f name="${repo#*/}" -F number="$1" \
    -f query='query($owner: String!, $name: String!, $number: Int!) { repository(owner: $owner, name: $name) { pullRequest(number: $number) { isInMergeQueue autoMergeRequest { enabledAt } } } }' \
    --jq '.data.repository.pullRequest | .isInMergeQueue or .autoMergeRequest != null'
}

# The numbers of the stack `$1`'s pull requests in the merge queue, as a JSON
# array.
queued_of() {
  local number members=()
  for number in $(jq -r '.[].number' <<< "$1"); do
    if [[ $(in_queue "$number") == true ]]; then members+=("$number"); fi
  done
  jq -cn '$ARGS.positional | map(tonumber)' --args "${members[@]}"
}

# Link the open chain `$1` on the server (`link.jq`): into the stack a member
# already belongs to, by that stack's number, so the stack's merged members
# stay below the open ones (#1275); otherwise as a new stack.
stack_link() {
  local number stacks=() args
  for number in $(jq -r '.[].number' <<< "$1"); do
    stacks+=("$(gh api graphql -f owner="${repo%/*}" -f name="${repo#*/}" -F number="$number" \
      -f query='query($owner: String!, $name: String!, $number: Int!) { repository(owner: $owner, name: $name) { pullRequest(number: $number) { stack { number } } } }' \
      --jq '.data.repository.pullRequest.stack.number // "null"')")
  done
  mapfile -t args < <(jq -cn --argjson chain "$(jq -c 'map(.number)' <<< "$1")" \
    '{chain: $chain, stacks: ($ARGS.positional | map(fromjson))}' --args "${stacks[@]}" | jq -r -f "$pr_stack_dir/link.jq")
  # No prompt is answered here: a question fails the link instead of waiting.
  gh stack link "${args[@]}" < /dev/null > /dev/null
}

# Rebase the stack `$1` (bottom to top) onto `origin/$trunk` and push every
# branch it moved, in one atomic push leased on each branch's remote tip. The
# rebase runs in a scratch worktree, detached, so no seat's checkout is
# touched: a branch checked out in another worktree moves on the server, and
# its seat's next fetch reads it. Prints one line per branch that moved.
# Refuses a stack whose branch does not contain the one below it, and stops
# at a conflict, naming the branch, with nothing pushed. The scratch is named
# for this process (`gandr-scratch-<pid>.`), and the caller's exit trap runs
# `drop_scratch`, so a failure anywhere removes it; a scratch a hard kill
# leaves, its process gone, is `wt:sweep`'s.
restack() {
  local stack=$1 heads head below fork scratch status=0 moved=() pushes=() leases=() old new
  mapfile -t heads < <(jq -r '.[].head' <<< "$stack")
  git fetch --quiet origin "$trunk" "${heads[@]}"
  below=
  for head in "${heads[@]}"; do
    if [[ -n "$below" ]] && ! git merge-base --is-ancestor "origin/$below" "origin/$head"; then
      echo "$head does not contain $below, the branch below it; rebase it onto $below first" >&2
      return 1
    fi
    below=$head
  done
  fork=$(git merge-base "origin/${heads[0]}" "origin/$trunk")
  scratch=$(mktemp -d "${TMPDIR:-/tmp}/gandr-scratch-$$.XXXXXX")
  pr_stack_scratch=$scratch
  git worktree add --quiet --detach "$scratch" "origin/${heads[-1]}"
  for head in "${heads[@]::${#heads[@]}-1}"; do
    git -C "$scratch" branch --quiet --force "pr-stack/$head" "origin/$head"
  done
  if ! git -C "$scratch" rebase --quiet --update-refs --onto "origin/$trunk" "$fork" > /dev/null; then
    local stopped conflicted=${heads[-1]}
    stopped=$(git -C "$scratch" rev-parse --verify --quiet REBASE_HEAD) || stopped=
    for head in "${heads[@]}"; do
      if [[ -n "$stopped" ]] && git merge-base --is-ancestor "$stopped" "origin/$head"; then conflicted=$head; break; fi
    done
    git -C "$scratch" rebase --abort || true
    echo "the restack of ${heads[*]} onto origin/$trunk conflicts in $conflicted; rebase $conflicted onto origin/$trunk by hand and land again" >&2
    status=1
  fi
  if (( status == 0 )); then
    for head in "${heads[@]}"; do
      old=$(git rev-parse "origin/$head")
      if [[ "$head" == "${heads[-1]}" ]]; then new=$(git -C "$scratch" rev-parse HEAD); else new=$(git -C "$scratch" rev-parse "pr-stack/$head"); fi
      [[ "$old" != "$new" ]] || continue
      pushes+=("$new:refs/heads/$head")
      leases+=("--force-with-lease=refs/heads/$head:$old")
      moved+=("$head ${old::12}..${new::12}")
    done
    if (( ${#pushes[@]} > 0 )); then
      git -C "$scratch" push --quiet --atomic "${leases[@]}" origin "${pushes[@]}" || status=$?
    fi
  fi
  for head in "${heads[@]::${#heads[@]}-1}"; do
    git branch --quiet --delete --force "pr-stack/$head" > /dev/null 2>&1 || true
  done
  drop_scratch
  (( status == 0 )) || return "$status"
  if (( ${#moved[@]} > 0 )); then printf 'moved %s\n' "${moved[@]}"; fi
  git fetch --quiet origin "${heads[@]}"
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

# Wait, every 30 seconds, until each of the trunk's required contexts on pull
# request `$1`'s head has concluded (`required.jq`, #1601); fail at the first
# reading with a required context red, naming it. The contexts are read from
# the rules, not through `gh pr checks --required`, so the wait never rests
# on gh's filter nor on the end of a run whose other jobs are not required.
wait_required() {
  local required reading
  required=$(required_contexts)
  while :; do
    reading=$(gh pr view "$1" -R "$repo" --json statusCheckRollup --jq .statusCheckRollup \
      | jq -c --argjson required "$required" -f "$pr_stack_dir/required.jq")
    if [[ $(jq '.failed | length' <<< "$reading") != 0 ]]; then
      echo "#$1's required checks are red: $(jq -r '.failed | join(", ")' <<< "$reading")" >&2
      return 1
    fi
    [[ $(jq '.pending | length' <<< "$reading") != 0 ]] || return 0
    sleep 30
  done
}

# Re-run the runs on pull request `$1`'s head that a twin on the same commit
# cancelled (`twins.jq`); succeeds when it re-ran one.
rerun_twins() {
  local sha ids id
  sha=$(gh pr view "$1" -R "$repo" --json headRefOid --jq .headRefOid)
  mapfile -t ids < <(gh run list -R "$repo" --commit "$sha" --event pull_request --limit 100 \
    --json databaseId,workflowName,startedAt,conclusion | jq -c -f "$pr_stack_dir/twins.jq" | jq -r '.[]')
  for id in "${ids[@]}"; do
    echo "#$1: re-running run $id, cancelled by its twin on ${sha::12}" >&2
    gh run rerun "$id" -R "$repo"
  done
  (( ${#ids[@]} > 0 ))
}

# Retarget to the trunk every open pull request the landing of `$1`, a JSON
# array of pull request numbers, would close (`retarget.jq`, #1420): GitHub
# deletes a merged branch and closes, unmerged, every open pull request still
# based on it that no linked stack carries. Each survives on the trunk, and
# `pr:land` from its top rebases it. Prints one line on stderr for each.
retarget_landing() {
  local number base
  while IFS=$'\t' read -r number base; do
    [[ -n "$number" ]] || continue
    gh pr edit "$number" -R "$repo" --base "$trunk" > /dev/null
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
# lands only once they have merged.
carried_queued() {
  local top number head members=()
  top=$(jq -r '.[-1].head' <<< "$1")
  git fetch --quiet origin "$top"
  while IFS=$'\t' read -r number head; do
    [[ -n "$number" && $(in_queue "$number") == true ]] || continue
    git fetch --quiet origin "$head" || continue
    if git merge-base --is-ancestor "origin/$head" "origin/$top"; then members+=("$number"); fi
  done < <(open_prs | jq -r --argjson stack "$1" '.[] | select(.number | IN($stack[].number) | not) | [.number, .head] | @tsv')
  jq -cn '$ARGS.positional | map(tonumber)' --args "${members[@]}"
}

# Queue the stack `$1`, bottom to top, up to and including pull request `$3`
# (#1988), past the members of the JSON array `$2` already in the merge
# queue. A stack of one is a plain landing, queued by auto-merge. A longer
# stack is linked on the server, only its open members when part of it is
# queued, and queued by GitHub's stack merge, which takes every member up to
# and including `$3` atomically. Every open pull request on a branch the
# landing deletes, outside it, is retargeted to the trunk first
# (`retarget_landing`). The stack merge refuses a pull request whose required
# checks are still expected, so each queued member's are waited on
# (`wait_required`), and a red one stops the landing, naming it. A cancelled
# run the rollup reads, left by a restack's twin runs, is re-run
# (`rerun_twins`), at most three times for a pull request. Returns 3 when the
# open members take no link above the queued ones: the stack is read again
# once those merge.
queue_stack() {
  local stack=$1 queued=$2 upto=$3 open landing number reruns watched
  open=$(jq -c --argjson queued "$queued" '[.[] | select(.number | IN($queued[]) | not)]' <<< "$stack")
  mapfile -t landing < <(jq -r --argjson upto "$upto" '(map(.number) | index($upto)) as $end | .[: $end + 1][].number' <<< "$open")
  retarget_landing "$(jq -cn '$ARGS.positional | map(tonumber)' --args "${landing[@]}")"
  if [[ $(jq length <<< "$stack") == 1 ]]; then
    gh pr merge "$upto" -R "$repo" --merge --auto
    return
  fi
  if [[ "$queued" == '[]' ]]; then
    stack_link "$stack"
  elif ! stack_link "$open" 2> /dev/null; then
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
# (`required.jq`): `green` when every one passed, `red` when one failed,
# `pending` otherwise.
required_state() {
  gh pr view "$1" -R "$repo" --json statusCheckRollup --jq .statusCheckRollup \
    | jq -c --argjson required "$2" -f "$pr_stack_dir/required.jq" \
    | jq -r 'if .failed != [] then "red" elif .pending != [] then "pending" else "green" end'
}

# Queue the largest ready prefix of pull request `$1`'s stack (`prefix.jq`,
# #1988). The members already queued are skipped; above them the members are
# read bottom up, and every one green on the trunk's required contexts is
# queued, up to the first red or pending one, which is named and where the
# reading stops. The tail above it is the next stack, landed the moment its
# own bottom goes green. `pr:land` runs this from any member, and `pr:watch`
# the moment its pull request goes green. Prints one line on stderr, and
# leaves its reading in `prefix_decision` (`prefix.jq`'s line),
# `prefix_server` (the stack) and `prefix_queued` (its queued members).
# Returns 0 when it queued a prefix or nothing was ready; 3 while a pull
# request queued on its own carries the stack's commits (`carried_queued`),
# or the open members take no link above the queued ones; `queue_stack`'s
# failure otherwise.
land_prefix() {
  local server queued carried required number state states=() decision verdict upto stop status=0
  server=$(server_stack "$1")
  [[ $(jq length <<< "$server") != 0 ]] || { echo "PR #$1 is not open" >&2; return 2; }
  queued=$(queued_of "$server")
  carried=$(carried_queued "$server")
  required=$(required_contexts)
  for number in $(jq -r --argjson queued "$queued" '.[].number | select(IN($queued[]) | not)' <<< "$server"); do
    state=$(required_state "$number" "$required")
    states+=("$number" "$state")
    [[ "$state" == green ]] || break
  done
  decision=$(jq -rn --argjson server "$server" --argjson queued "$queued" --argjson carried "$carried" \
    --argjson states "$(jq -cn '$ARGS.positional as $p | [range(0; $p | length; 2) | {key: $p[.], value: $p[. + 1]}] | from_entries' --args "${states[@]}")" \
    '{server: $server, queued: $queued, carried: $carried, states: $states}' | jq -r -f "$pr_stack_dir/prefix.jq")
  prefix_decision=$decision prefix_server=$server prefix_queued=$queued
  verdict= upto= stop= state=
  IFS=$'\t' read -r verdict upto stop state <<< "$decision"
  case "$verdict" in
    wait)
      echo "#$upto, queued on its own, carries this stack's commits; the stack lands once it merges" >&2
      return 3
      ;;
    queued) echo "the stack is queued up to its top, #$(jq -r '.[-1].number' <<< "$server")" >&2 ;;
    hold) echo "nothing lands: #$upto is $stop, and the stack lands from it once it is green" >&2 ;;
    land)
      hold_landing "$(jq -c --argjson queued "$queued" --argjson upto "$upto" \
        '[.[].number | select(IN($queued[]) | not)] | .[: index($upto) + 1]' <<< "$server")"
      queue_stack "$server" "$queued" "$upto" || status=$?
      release_landing
      (( status == 0 )) || return "$status"
      echo "queued the stack up to #$upto${stop:+; #$stop above it is $state, and the stack lands from it once it is green}" >&2
      ;;
    *) echo "unexpected landing decision: $decision" >&2; return 2 ;;
  esac
}
