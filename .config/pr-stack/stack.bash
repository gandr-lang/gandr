# The stacking rule, mechanical (#1264), sourced by `pr:open`, `pr:land` and
# `pr:watch`. The server is the only record: every reading is of the open pull
# requests, and every stack is linked with `gh stack link`, which keeps no
# local state. Rebase order is the invariant: each branch sits on the one
# below it, and a restack moves the whole chain in one push.
#
# The caller sets `repo` (owner/name) and `trunk` (the default branch).

pr_stack_dir="$(git rev-parse --show-toplevel)/.config/pr-stack"

# The open pull requests that land, drafts left out, as a JSON array of
# `{number, head, base, created}`.
open_prs() {
  gh pr list -R "$repo" --state open --limit 200 --json number,headRefName,baseRefName,isDraft,createdAt \
    --jq '[.[] | select(.isDraft | not) | {number, head: .headRefName, base: .baseRefName, created: .createdAt}]'
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

# Whether pull request `$1` is in the merge queue.
in_queue() {
  gh api graphql -f owner="${repo%/*}" -f name="${repo#*/}" -F number="$1" \
    -f query='query($owner: String!, $name: String!, $number: Int!) { repository(owner: $owner, name: $name) { pullRequest(number: $number) { isInMergeQueue } } }' \
    --jq .data.repository.pullRequest.isInMergeQueue
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

# Rebase the stack `$1` (bottom to top) onto `origin/$trunk` and push every
# branch it moved, in one atomic push leased on each branch's remote tip. The
# rebase runs in a scratch worktree, detached, so no seat's checkout is
# touched: a branch checked out in another worktree moves on the server, and
# its seat's next fetch reads it. Prints one line per branch that moved.
# Refuses a stack whose branch does not contain the one below it, and stops
# at a conflict, naming the branch, with nothing pushed.
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
  scratch=$(mktemp -d)
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
  git worktree remove --force "$scratch"
  (( status == 0 )) || return "$status"
  if (( ${#moved[@]} > 0 )); then printf 'moved %s\n' "${moved[@]}"; fi
  git fetch --quiet origin "${heads[@]}"
}

# Link the stack `$1` on the server and queue it as one group; a stack of one
# is a plain landing, queued by auto-merge once its checks pass. An atomic
# stack merge refuses a pull request whose required checks are still
# expected, so each one's required checks are waited on first, and a red one
# stops the landing, naming it.
queue_stack() {
  local stack=$1 numbers number
  mapfile -t numbers < <(jq -r '.[].number' <<< "$stack")
  if (( ${#numbers[@]} == 1 )); then
    gh pr merge "${numbers[0]}" -R "$repo" --merge --auto
    return
  fi
  gh stack link "${numbers[@]}" > /dev/null
  for number in "${numbers[@]}"; do
    if ! gh pr checks "$number" -R "$repo" --required --watch --fail-fast --interval 30 > /dev/null; then
      echo "#$number's required checks failed; fix it, then land the stack again" >&2
      return 1
    fi
  done
  gh stack merge "${numbers[-1]}" --yes --merge
}
