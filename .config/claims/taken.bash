#!/usr/bin/env bash
# The gate refuses a unit branch whose issue holds no claim of its lane
# (#5146), so a lane that works a unit without a claim claims it at its first
# gate, and `claim:next` gives the unit to no other lane. `taken.jq` reads the
# branch and the claim. A branch that works no unit reads nothing. A failed
# read of the issue leaves the gate to run as before and says so.
set -euo pipefail
root=$(git rev-parse --show-toplevel)
claims=$root/.config/claims
branch=$(git branch --show-current)
lanes=$(yq -p toml -o json '.lane | keys' "$root/.config/issues/lanes.toml")
unit=$(jq -nc -L "$claims" --arg branch "$branch" --argjson lanes "$lanes" \
  '{step: "branch", branch: $branch, lanes: $lanes}' | jq -c -L "$claims" -f "$claims/taken.jq")
[[ $unit != null ]] || exit 0
number=$(jq -r .number <<< "$unit")
issue=null
if read=$(gh api "repos/{owner}/{repo}/issues/$number" --jq '{number, state, labels: [.labels[].name], body: (.body // "")}' 2> /dev/null); then
  issue=$read
fi
verdict=$(jq -nc --arg branch "$branch" --argjson lanes "$lanes" --argjson issue "$issue" \
  '{step: "gate", branch: $branch, lanes: $lanes, issue: $issue}' | jq -c -L "$claims" -f "$claims/taken.jq")
case $(jq -r .verdict <<< "$verdict") in
  refused)
    jq -r .line <<< "$verdict" >&2
    exit 1
    ;;
  unread) jq -r .line <<< "$verdict" >&2 ;;
esac
