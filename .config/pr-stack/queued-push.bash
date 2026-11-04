#!/usr/bin/env bash
# The push tier's queue guard (#2531): refuse a push to a branch whose pull
# request is in the merge queue, set to enter it or held for it by a waiting
# `pr:land`, or to a branch below such a pull request (`queued.jq`). The push
# would eject it and every member above, and the whole chain's checks would
# run again; work found while a pull request waits goes in the next pull
# request on top. prek runs it at `pre-push` with the pushed branch in
# `PRE_COMMIT_REMOTE_BRANCH`. A reading that fails refuses too, naming the
# failure. `git push --no-verify` stays the owner's.
set -euo pipefail
branch=${PRE_COMMIT_REMOTE_BRANCH:-}
branch=${branch#refs/heads/}
[[ -n "$branch" ]] || exit 0
repo=$(gh repo view --json nameWithOwner --jq .nameWithOwner)
trunk=$(gh repo view "$repo" --json defaultBranchRef --jq .defaultBranchRef.name)
[[ "$branch" != "$trunk" ]] || exit 0
source "$(git rev-parse --show-toplevel)/.config/pr-stack/stack.bash"
blocking=$(open_prs | jq -c --arg branch "$branch" -f "$pr_stack_dir/queued.jq")
[[ "$blocking" != "[]" ]] || exit 0
state=$(jq -r 'map("#\(.number) \(if .state == "queued" then "in the merge queue" else "held for it (the `landing` label)" end)") | join(", ")' <<< "$blocking")
echo "push refused: $branch would eject $state, and the chain's checks would run again; put the work in the next pull request on top (\`pr:open\`)" >&2
exit 1
