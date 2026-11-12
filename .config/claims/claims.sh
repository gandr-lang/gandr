#!/usr/bin/env bash
# The claim lifecycle (#1270), run by `.github/workflows/claims.yml`:
#
#   claims.sh merged [--dry-run]   after a merge; the body is $CLAIMS_MERGED_BODY
#   claims.sh sweep [--dry-run]    the scheduled sweep
#
# It reads the claimed issues, open and closed (a `Closes #n` merge closes the
# issue before this runs, and GitHub keeps its labels), the open pull
# requests, and when each claim's label was last added, through the API: a
# claim ages by its label, never by the issue's last update (#3915). It
# lets `decide.jq` pick the claims that come off, removes the
# label from each and prints one line per removal; nothing is posted for a
# removal. A silent claim's lapse also takes its lane's claim marker off the
# body, so the body agrees with the label (#5531). A merge then writes a
# release marker on each open issue it advanced, naming the lane its branch
# opens with (`markers.jq`), so that lane claims the continuation first for 2
# hours (`next.jq`, #3915). It ticks the
# rows of each `collector` it advances and closes one it leaves with no open
# row (#3732). `--dry-run` prints the removals, the releases and the rows
# without making them.
set -euo pipefail
mode=${1:?usage: claims.sh merged|sweep [--dry-run]}
dry=${2:-}
# shellcheck source=/dev/null
source "$(dirname "${BASH_SOURCE[0]}")/../gh/repo.bash"
repo=$(repo_name)
here=$(dirname "${BASH_SOURCE[0]}")
label=status:claimed

case "$mode" in
  merged) merged=$(jq -n 'env.CLAIMS_MERGED_BODY // ""') ;;
  sweep) merged=null ;;
  *) echo "unknown mode: $mode" >&2; exit 2 ;;
esac

# GitHub closes the issue that a closing keyword names only when the pull
# request merges into the default branch. A unit lands on the trunk,
# `landing` (#5443), so a merge into any other branch closes each such issue
# here, as GitHub would. The run then reads the issue as closed.
base=${CLAIMS_MERGED_BASE:-}
if [[ $mode == merged && -n $base && $base != "${CLAIMS_DEFAULT_BRANCH:-main}" ]]; then
  for number in $(jq -rn -L "$here" 'include "targets"; env.CLAIMS_MERGED_BODY // "" | targets(closing) | unique[]'); do
    if [[ "$dry" == --dry-run ]]; then
      printf 'would close #%s\n' "$number"
      continue
    fi
    if [[ $(gh issue view "$number" -R "$repo" --json state --jq .state) == OPEN ]]; then
      gh issue close "$number" -R "$repo" --reason completed \
        --comment "The landing${CLAIMS_MERGED_NUMBER:+ #$CLAIMS_MERGED_NUMBER} on \`$base\` closes this issue." > /dev/null
      printf 'closed #%s (the landing on %s)\n' "$number" "$base"
    fi
  done
fi

# Each claim's lane is its body's first claim marker at this reading (#5531).
# The listing keeps the lane and drops the body, so each later reading of the
# listing stays small.
listed=$(gh api --paginate "repos/$repo/issues?state=all&labels=$label&per_page=100" \
  --jq '[.[] | select(.pull_request == null) | {number, state, labels: [.labels[].name], created_at, updated_at, body}]' \
  | jq -s -L "$here" 'include "markers"; add // [] | map(.lane = (.body | claim_lane) | del(.body))')
open_prs=$(gh api --paginate "repos/$repo/pulls?state=open&per_page=100" \
  --jq '[.[] | {number, body: (.body // ""), head: .head.ref}]' | jq -s 'add // []')
# The claims whose label's age the sweep reads from their events (#5078):
# open, no epic, named by no open pull request, and on an issue that changed
# in the last 4 hours. Any other claim's age decides nothing, or its issue's
# last update, which a label's addition sets, already shows the label is 4
# hours old. A merge's run reads no events: it finds a claim silent by that
# last update alone, and the sweep, every two hours, reads the busy ones.
declare -A aged=()
if [[ $mode == sweep ]]; then
  while IFS= read -r number; do
    [[ -n $number ]] && aged[$number]=1
  done < <(jq -r -L "$here" --argjson now "$(date +%s)" --argjson prs "$open_prs" 'include "targets";
    .[] | . as $issue
    | select(.state == "open" and (.labels | index("kind:epic") | not)
        and ([$prs[] | names($issue.number)] | any | not) and ($now - (.updated_at | fromdateiso8601)) < 14400)
    | .number' <<< "$listed")
fi
# A label no `labeled` event shows (a transferred issue) ages from the issue's
# creation.
claimed=$(jq -c '.[]' <<< "$listed" | while IFS= read -r issue; do
  number=$(jq -r .number <<< "$issue")
  if [[ -n ${aged[$number]:-} ]]; then
    at=$(gh api --paginate "repos/$repo/issues/$number/events?per_page=100" \
      --jq "[.[] | select(.event == \"labeled\" and .label.name == \"$label\") | .created_at] | last // empty" | awk 'NF { at = $0 } END { print at }')
    jq -c --arg at "$at" '{number, state, labels, claimed_at: (if $at == "" then .created_at else $at end)}' <<< "$issue"
  else
    jq -c '{number, state, labels, claimed_at: .updated_at}' <<< "$issue"
  fi
done | jq -s .)

removals=$(jq -rn --argjson now "$(date +%s)" --argjson claimed "$claimed" --argjson open_prs "$open_prs" --argjson merged "$merged" \
  '{now: $now, claimed: $claimed, open_prs: $open_prs, merged_body: $merged}' | jq -r -L "$here" -f "$here/decide.jq")

# unmark <number>: takes the claim marker of the lane whose silent claim
# lapsed off the body, after its label comes off (#5531). The lane is the one
# the listing read. The body is read again after the label comes off: a lane
# that claims the issue in between writes its marker alone, so the lapse
# step finds no marker of the lapsed lane and writes nothing. A failed read or
# write leaves the marker, which holds no claim without the label, and the
# next claim of the issue drops it.
unmark() {
  local number=$1 held body
  held=$(jq -r --argjson n "$number" '.[] | select(.number == $n) | .lane // empty' <<< "$listed")
  [[ -n $held ]] || return 0
  if [[ "$dry" == --dry-run ]]; then
    printf 'would unmark #%s: %s\n' "$number" "$held"
    return 0
  fi
  if ! body=$(gh api "repos/$repo/issues/$number" --jq '{body}' \
    | jq -c --arg lane "$held" '{lane: $lane, step: "lapse", body}' | jq -c -L "$here" -f "$here/claimed.jq"); then
    echo "could not read #$number to unmark $held" >&2
    return 0
  fi
  [[ $(jq '.body != null' <<< "$body") == true ]] || return 0
  if gh api -X PATCH "repos/$repo/issues/$number" --input - <<< "$body" > /dev/null; then
    printf 'unmarked #%s: %s\n' "$number" "$held"
  else
    echo "could not unmark #$number: $held" >&2
  fi
}

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
  if [[ $reason == silent ]]; then
    unmark "$number"
  fi
done <<< "$removals"
printf '%s: %d of %d claims removed\n' "$mode" "$count" "$(jq length <<< "$claimed")"

[[ $mode == merged ]] || exit 0

# The lane a merged branch names (#3915): the longest lane of the factory's
# lane table (`lanes.bash`) the branch is, or opens with before a `-`. With
# no table, as on a hosted runner, it is the letters before the branch's
# first number.
head=${CLAIMS_MERGED_HEAD:-}
# shellcheck source=/dev/null
source "$here/lanes.bash"
lane=$(lanes_keys | jq -r --arg head "$head" '[.[] | select(. as $l | $head == $l or ($head | startswith($l + "-")))] | max_by(length) // ""')
[[ -n $lane ]] || lane=$(sed -nE 's/^([a-z]+(-[a-z]+)*)-[0-9].*$/\1/p' <<< "$head")
if [[ -n $lane ]]; then
  at=$(date -u +%Y-%m-%dT%H:%M:%SZ)
  while IFS=$'\t' read -r number reason; do
    [[ $reason == advanced ]] || continue
    issue=$(gh api "repos/$repo/issues/$number" --jq '{state, body: (.body // "")}')
    [[ $(jq -r .state <<< "$issue") == open ]] || continue
    if [[ "$dry" == --dry-run ]]; then
      printf 'would release #%s to %s\n' "$number" "$lane"
      continue
    fi
    jq -c -L "$here" --arg lane "$lane" --arg at "$at" 'include "markers"; {body: (.body | marked(released_marker($lane; $at)))}' <<< "$issue" \
      | gh api -X PATCH "repos/$repo/issues/$number" --input - > /dev/null
    printf 'released #%s to %s\n' "$number" "$lane"
  done <<< "$removals"
fi

# A merge that advances a `collector` ticks the rows its body's `## Rows`
# names, and a collector it leaves with no open row closes, its comment naming
# the landing (#3732, `landed.jq`). The landing is $CLAIMS_MERGED_NUMBER.
# Two landings that advance one collector and merge at once read the same
# body, so each merge also ticks the rows of the merged landings on the
# collector's timeline, and the later write keeps the earlier's ticks (#5583).
advanced=$(jq -rn -L "$here" 'include "targets"; env.CLAIMS_MERGED_BODY // "" | targets("advances") | unique[]')
[[ -n $advanced ]] || exit 0
landing=${CLAIMS_MERGED_NUMBER:-}
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT

# landings <number>: the bodies of the merged pull requests of this repository
# on the timeline of the issue <number>, as one JSON array. A failed read
# gives none, so the merged body's own rows still tick, and the next merge or
# a tick by hand takes the rest.
landings() {
  local read
  if read=$(gh api --paginate "repos/$repo/issues/$1/timeline?per_page=100" \
    --jq ".[] | select(.event == \"cross-referenced\" and .source.issue.pull_request.merged_at != null and (.source.issue.repository_url | endswith(\"/repos/$repo\"))) | .source.issue.body // \"\" | tojson"); then
    jq -cs . <<< "$read"
  else
    echo "could not read the timeline of #$1: only the merged body's rows tick" >&2
    echo '[]'
  fi
}

issues=$(for number in $advanced; do
  issue=$(gh api "repos/$repo/issues/$number" --jq 'select(.state == "open" and .pull_request == null) | {number, labels: [.labels[].name], body: (.body // "")}')
  [[ -n $issue ]] || continue
  if [[ $(jq '.labels | index("collector") != null' <<< "$issue") == true ]]; then
    landings "$number" > "$scratch/landings.json"
    jq -c --slurpfile landings "$scratch/landings.json" '. + {landings: $landings[0]}' <<< "$issue"
  else
    printf '%s\n' "$issue"
  fi
done | jq -s .)
jq -c '{body: (env.CLAIMS_MERGED_BODY // ""), issues: .}' <<< "$issues" \
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
