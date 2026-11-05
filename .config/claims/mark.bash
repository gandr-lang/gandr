# The claim that `claim:next` and `claim:take` write (#5175), sourced by both.
# `claimed.jq` holds the rule: the write keeps another lane's claim marker
# standing before the lane's own, and the check reads which marker stands
# first (#4660).

mark_here=$(dirname "${BASH_SOURCE[0]}")

# claim_mark <repo> <number> <lane> <read>: claims issue <number> for <lane>.
# It adds `status:claimed` and writes the body on standard input, `{body}`
# with the lane's marker. Then it reads the issue once more into the file
# <read>, `{labels, body}`, and sets `claim_kept` to `true` when the lane's
# marker stands first. When another lane's marker stands first, the earlier
# claim keeps the issue: it takes the lane's own marker off and sets
# `claim_kept` to `false`. The answer is a variable, not the exit status, so
# a failed call stops the caller under `set -e` as before.
claim_mark() {
  local repo=$1 number=$2 lane=$3 read=$4 check
  gh api -X POST "repos/$repo/issues/$number/labels" -f 'labels[]=status:claimed' > /dev/null
  gh api -X PATCH "repos/$repo/issues/$number" --input - > /dev/null
  gh api "repos/$repo/issues/$number" --jq '{labels: [.labels[].name], body}' > "$read"
  check=$(jq -c --arg lane "$lane" '{lane: $lane, step: "check", body}' "$read" \
    | jq -c -L "$mark_here" -f "$mark_here/claimed.jq")
  claim_kept=$(jq .kept <<< "$check")
  [[ $claim_kept == true ]] && return
  claim_kept=false
  if [[ $(jq '.body != null' <<< "$check") == true ]]; then
    jq -c '{body}' <<< "$check" | gh api -X PATCH "repos/$repo/issues/$number" --input - > /dev/null
  fi
}
