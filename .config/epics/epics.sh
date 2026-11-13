#!/usr/bin/env bash
# An epic closes itself when every issue it is blocked by and every sub-issue
# it holds is closed (#3398, #4972), run by `.github/workflows/tracker-close-epics.yml` on
# every closed issue, or by hand:
#
#   epics.sh <issue> [--dry-run]
#
# It reads the epics the closed one blocks and the epic it sits under, and
# for each the issues that epic is blocked by and its sub-issues, through the
# API, and lets `close.jq` decide. It first sets the epic blocked by each open
# sub-issue that `close.jq` names, so the two lists agree and that sub-issue
# wakes the epic when it closes. On `close` it closes the epic with a comment
# under `<!-- epic-closed -->` naming them; on `list` (an epic in another
# repository) and `keep` it prints the reason and closes nothing. An epic
# with no unit is never closed: its units are not linked yet. `--dry-run`
# prints each decision and each link without acting on it.
set -euo pipefail
issue=${1:?usage: epics.sh <issue> [--dry-run]}
dry=${2:-}
# shellcheck source=/dev/null
source "$(dirname "${BASH_SOURCE[0]}")/../gh/repo.bash"
repo=$(repo_name)
here=$(dirname "${BASH_SOURCE[0]}")
# shellcheck source=/dev/null
source "$here/../issues/deps.bash"
api=https://api.github.com/
shape='{number, repository: (.repository_url | ltrimstr("'"$api"'repos/")), state, labels: [.labels[].name]}'

blocking=$(gh api --paginate "repos/$repo/issues/$issue/dependencies/blocking?per_page=100" \
  --jq "[.[] | $shape | select(.labels | index(\"kind:epic\"))]" | jq -s 'add // []')
# An issue under no parent reads as a 404, and any other failure stops the run.
err=$(mktemp)
trap 'rm -f "$err"' EXIT
if parent=$(gh api "repos/$repo/issues/$issue/parent" --jq "[$shape | select(.labels | index(\"kind:epic\"))]" 2> "$err"); then
  :
elif [[ $(< "$err") == *"HTTP 404"* ]]; then
  parent='[]'
else
  cat "$err" >&2
  exit 1
fi
epics=$(jq -n --argjson blocking "$blocking" --argjson parent "$parent" '$blocking + $parent | unique_by([.repository, .number])')
if [[ $(jq length <<< "$epics") == 0 ]]; then
  echo "#$issue blocks no epic and sits under none"
  exit 0
fi

while read -r number epic_repo; do
  # Read again: a sibling closing in the same seconds may have closed it.
  epic=$(gh api "repos/$epic_repo/issues/$number" --jq "$shape")
  blocked_by=$(gh api --paginate "repos/$epic_repo/issues/$number/dependencies/blocked_by?per_page=100" \
    --jq "[.[] | $shape | del(.labels)]" | jq -s 'add // []')
  sub_issues=$(gh api --paginate "repos/$epic_repo/issues/$number/sub_issues?per_page=100" \
    --jq "[.[] | $shape | del(.labels)]" | jq -s 'add // []')
  decision=$(jq -rn --arg repo "$repo" --argjson closed "$issue" --argjson epic "$epic" \
    --argjson blocked_by "$blocked_by" --argjson sub_issues "$sub_issues" \
    '{repo: $repo, closed: $closed, epic: $epic, blocked_by: $blocked_by, sub_issues: $sub_issues}' | jq -r -f "$here/close.jq")
  IFS=$'\t' read -r action reason links <<< "$decision"
  for unit in $links; do
    if [[ "$dry" == --dry-run ]]; then
      printf 'would set #%s blocked by #%s\n' "$number" "$unit"
    else
      deps_set_block "$repo" "$number" "$unit"
    fi
  done
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
