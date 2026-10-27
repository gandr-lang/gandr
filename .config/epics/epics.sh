#!/usr/bin/env bash
# An epic's closing is a ruling, not an event (#2973), asked for by
# `.github/workflows/epics.yml` on every closed issue, or by hand:
#
#   epics.sh <issue> [--dry-run]
#
# It reads the closed issue's parent and the parent's sub-issues through the
# API and lets `close.jq` decide. On `ask` it labels the epic
# `needs:close-ruling` and comments the reason under `<!-- epic-complete -->`,
# closing nothing: the coordinator closes the epic or files its next unit,
# and `stall:watch` pages the coordinator while the label stands. On `list`
# (an epic in another repository) and `keep` it prints the reason and
# changes nothing. `--dry-run` prints the decision without acting on it.
set -euo pipefail
issue=${1:?usage: epics.sh <issue> [--dry-run]}
dry=${2:-}
repo=${GITHUB_REPOSITORY:-$(gh repo view --json nameWithOwner --jq .nameWithOwner)}
here=$(dirname "${BASH_SOURCE[0]}")
api=https://api.github.com/

parent_url=$(gh api "repos/$repo/issues/$issue" --jq '.parent_issue_url // empty')
if [[ -z "$parent_url" ]]; then
  echo "#$issue has no parent"
  exit 0
fi
parent=$(gh api "${parent_url#"$api"}" --jq '{number, repository: (.repository_url | ltrimstr("'"$api"'repos/")), state, labels: [.labels[].name]}')
sub_issues=$(gh api --paginate "${parent_url#"$api"}/sub_issues?per_page=100" \
  --jq '[.[] | {number, repository: (.repository_url | ltrimstr("'"$api"'repos/")), state}]' | jq -s 'add // []')

decision=$(jq -rn --arg repo "$repo" --argjson closed "$issue" --argjson parent "$parent" --argjson sub_issues "$sub_issues" \
  '{repo: $repo, closed: $closed, parent: $parent, sub_issues: $sub_issues}' | jq -r -f "$here/close.jq")
IFS=$'\t' read -r action reason <<< "$decision"
epic=$(jq -r .number <<< "$parent")

case "$action" in
  ask)
    if [[ "$dry" == --dry-run ]]; then
      printf 'would ask for a ruling on #%s: %s\n' "$epic" "$reason"
      exit 0
    fi
    # A sibling closing in the same seconds may have asked already.
    if jq -e '.labels | index("needs:close-ruling")' <<< "$parent" > /dev/null; then
      printf 'left #%s: it already awaits its close ruling\n' "$epic"
      exit 0
    fi
    gh issue edit "$epic" --repo "$repo" --add-label needs:close-ruling > /dev/null
    printf '<!-- epic-complete -->\n%s\n' "$reason" | gh issue comment "$epic" --repo "$repo" --body-file - > /dev/null
    printf 'asked for a ruling on #%s: %s\n' "$epic" "$reason"
    ;;
  list) printf 'not asked: %s; its last sub-issue #%s closed\n' "$reason" "$issue" ;;
  keep) printf 'left #%s: %s\n' "$epic" "$reason" ;;
  *) echo "close.jq gave no decision for #$issue" >&2; exit 1 ;;
esac
