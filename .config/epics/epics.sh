#!/usr/bin/env bash
# An epic closes itself when every issue it is blocked by is closed (#3398),
# run by `.github/workflows/epics.yml` on every closed issue, or by hand:
#
#   epics.sh <issue> [--dry-run]
#
# It reads the issues the closed one blocks, and for each that is an epic
# the issues it is blocked by, through the API, and lets `close.jq` decide.
# On `close` it closes the epic with a comment under `<!-- epic-closed -->`
# naming them; on `list` (an epic in another repository) and `keep` it prints
# the reason and changes nothing. An epic blocked by nothing is never closed:
# its units are not linked yet. `--dry-run` prints each decision without
# acting on it.
set -euo pipefail
issue=${1:?usage: epics.sh <issue> [--dry-run]}
dry=${2:-}
repo=${GITHUB_REPOSITORY:-$(gh repo view --json nameWithOwner --jq .nameWithOwner)}
here=$(dirname "${BASH_SOURCE[0]}")
api=https://api.github.com/
shape='{number, repository: (.repository_url | ltrimstr("'"$api"'repos/")), state, labels: [.labels[].name]}'

epics=$(gh api --paginate "repos/$repo/issues/$issue/dependencies/blocking?per_page=100" \
  --jq "[.[] | $shape | select(.labels | index(\"kind:epic\"))]" | jq -s 'add // []')
if [[ $(jq length <<< "$epics") == 0 ]]; then
  echo "#$issue blocks no epic"
  exit 0
fi

while read -r number epic_repo; do
  # Read again: a sibling closing in the same seconds may have closed it.
  epic=$(gh api "repos/$epic_repo/issues/$number" --jq "$shape")
  blocked_by=$(gh api --paginate "repos/$epic_repo/issues/$number/dependencies/blocked_by?per_page=100" \
    --jq "[.[] | $shape | del(.labels)]" | jq -s 'add // []')
  decision=$(jq -rn --arg repo "$repo" --argjson closed "$issue" --argjson epic "$epic" --argjson blocked_by "$blocked_by" \
    '{repo: $repo, closed: $closed, epic: $epic, blocked_by: $blocked_by}' | jq -r -f "$here/close.jq")
  IFS=$'\t' read -r action reason <<< "$decision"
  case "$action" in
    close)
      if [[ "$dry" == --dry-run ]]; then
        printf 'would close #%s: %s\n' "$number" "$reason"
        continue
      fi
      printf '<!-- epic-closed -->\n%s\n' "$reason" | gh issue comment "$number" --repo "$repo" --body-file - > /dev/null
      gh issue close "$number" --repo "$repo" --reason completed > /dev/null
      printf 'closed #%s: %s\n' "$number" "$reason"
      ;;
    list) printf 'not closed: %s; #%s closed\n' "$reason" "$issue" ;;
    keep) printf 'left: %s\n' "$reason" ;;
    *) echo "close.jq gave no decision for #$number" >&2; exit 1 ;;
  esac
done < <(jq -r '.[] | "\(.number) \(.repository)"' <<< "$epics")
