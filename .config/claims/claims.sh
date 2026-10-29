#!/usr/bin/env bash
# The claim lifecycle (#1270), run by `.github/workflows/claims.yml`:
#
#   claims.sh merged [--dry-run]   after a merge; the body is $CLAIMS_MERGED_BODY
#   claims.sh sweep [--dry-run]    the scheduled sweep
#
# It reads the claimed issues, open and closed (a `Closes #n` merge closes the
# issue before this runs, and GitHub keeps its labels), and the open pull
# requests through the API, lets `decide.jq` pick the claims that come off,
# removes the label from each and prints one line per removal; nothing is
# posted for a removal. A merge then ticks the rows of each `collector` it
# advances and closes one it leaves with no open row (#3732). `--dry-run`
# prints the removals and the rows without making them.
set -euo pipefail
mode=${1:?usage: claims.sh merged|sweep [--dry-run]}
dry=${2:-}
repo=${GITHUB_REPOSITORY:-$(gh repo view --json nameWithOwner --jq .nameWithOwner)}
here=$(dirname "${BASH_SOURCE[0]}")
label=status:claimed

case "$mode" in
  merged) merged=$(jq -n 'env.CLAIMS_MERGED_BODY // ""') ;;
  sweep) merged=null ;;
  *) echo "unknown mode: $mode" >&2; exit 2 ;;
esac

claimed=$(gh api --paginate "repos/$repo/issues?state=all&labels=$label&per_page=100" \
  --jq '[.[] | select(.pull_request == null) | {number, state, labels: [.labels[].name], updated_at}]' | jq -s 'add // []')
open_prs=$(gh api --paginate "repos/$repo/pulls?state=open&per_page=100" \
  --jq '[.[] | {number, body: (.body // ""), head: .head.ref}]' | jq -s 'add // []')

removals=$(jq -rn --argjson now "$(date +%s)" --argjson claimed "$claimed" --argjson open_prs "$open_prs" --argjson merged "$merged" \
  '{now: $now, claimed: $claimed, open_prs: $open_prs, merged_body: $merged}' | jq -r -L "$here" -f "$here/decide.jq")

count=0
while IFS=$'\t' read -r number reason; do
  [[ -n "$number" ]] || continue
  if [[ "$dry" != --dry-run ]] && ! gh api -X DELETE "repos/$repo/issues/$number/labels/${label/:/%3A}" > /dev/null; then
    # A merge's run and a sweep may remove one label at once (#2470): the
    # removal that finds it gone is done, any other failure is not.
    if gh api "repos/$repo/issues/$number/labels" --jq '.[].name' | grep -qxF "$label"; then
      echo "could not unclaim #$number" >&2
      exit 1
    fi
    printf 'already unclaimed #%s: %s\n' "$number" "$reason"
    continue
  fi
  printf 'unclaimed #%s: %s\n' "$number" "$reason"
  count=$((count + 1))
done <<< "$removals"
printf '%s: %d of %d claims removed\n' "$mode" "$count" "$(jq length <<< "$claimed")"

# A merge that advances a `collector` ticks the rows its body's `## Rows`
# names, and a collector it leaves with no open row closes, its comment naming
# the landing (#3732, `landed.jq`). The landing is $CLAIMS_MERGED_NUMBER.
[[ $mode == merged ]] || exit 0
advanced=$(jq -rn -L "$here" 'include "targets"; env.CLAIMS_MERGED_BODY // "" | targets("advances") | unique[]')
[[ -n $advanced ]] || exit 0
issues=$(for number in $advanced; do
  gh api "repos/$repo/issues/$number" --jq 'select(.state == "open" and .pull_request == null) | {number, labels: [.labels[].name], body: (.body // "")}'
done | jq -s .)
landing=${CLAIMS_MERGED_NUMBER:-}
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
jq -n --argjson issues "$issues" '{body: (env.CLAIMS_MERGED_BODY // ""), issues: $issues}' \
  | jq -c -L "$here" -f "$here/landed.jq" \
  | while IFS= read -r landed; do
      number=$(jq -r .number <<< "$landed")
      close=$(jq -r .close <<< "$landed")
      if [[ "$dry" == --dry-run ]]; then
        printf 'would tick the rows of #%s%s\n' "$number" "$([[ $close == true ]] && echo ', and close it')"
        continue
      fi
      jq -r .body <<< "$landed" > "$scratch/body.md"
      gh issue edit "$number" -R "$repo" --body-file "$scratch/body.md" > /dev/null
      printf 'ticked the rows of #%s\n' "$number"
      if [[ $close == true ]]; then
        gh issue close "$number" -R "$repo" --comment "The landing${landing:+ #$landing} clears the last open row, so the collector closes." > /dev/null
        printf 'closed #%s%s\n' "$number" "${landing:+ (the landing: #$landing)}"
      fi
    done
