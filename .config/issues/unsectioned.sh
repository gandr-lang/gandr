#!/usr/bin/env bash
# Every issue is a unit or is flagged (#3113), run by
# `.github/workflows/issues.yml` on every opened, edited, labelled or
# unlabelled issue, or by hand:
#
#   unsectioned.sh <issue>
#
# A body the unit form wrote is first made a unit's body, its kind and areas
# set as labels (`form.jq`), and `needs:triage` settled on them
# (`triage.sh`): the workflow's own edits start no run. Then `unit:check`'s
# reading of the body (`.config/claims/unit.jq`, the sections alone: the
# dependencies and vault names are `unit:check`'s) decides, through
# `unsectioned.jq`, whether `status:unsectioned` goes on or comes off and how
# the one `<!-- unit:check -->` comment reads. It reads the issue as it
# stands now, so runs arriving out of order settle on the last state.
set -euo pipefail
issue=${1:?usage: unsectioned.sh <issue>}
# shellcheck source=/dev/null
source "$(dirname "${BASH_SOURCE[0]}")/../gh/repo.bash"
repo=$(repo_name)
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
root=$(cd "$here/../.." && pwd)

issued=$(gh api "repos/$repo/issues/$issue")
if [[ $(jq '.pull_request != null' <<< "$issued") == true ]]; then
  echo "#$issue is a pull request; only issues are read"
  exit 0
fi
form=$(jq -r '.body // ""' <<< "$issued" | jq -R -s -c -f "$here/form.jq")
if [[ $form != null ]]; then
  gh api -X PATCH "repos/$repo/issues/$issue" -f body="$(jq -r .body <<< "$form")" > /dev/null
  labels=()
  while IFS= read -r label; do labels+=(--add-label "$label"); done < <(jq -r '.labels[]' <<< "$form")
  if (( ${#labels[@]} > 0 )); then gh issue edit "$issue" --repo "$repo" "${labels[@]}" > /dev/null; fi
  echo "#$issue: the form's fields written as sections, labelled $(jq -r '.labels | join(" ")' <<< "$form")"
  "$root/.config/triage/triage.sh" "$issue"
  issued=$(gh api "repos/$repo/issues/$issue")
fi
concerns=$(jq -R -s -c -f "$here/concerns.jq" "$root/ledger/concerns.sql")
findings=$(jq -r '.body // ""' <<< "$issued" \
  | jq -R -s -r -L "$root/.config/claims" --argjson concerns "$concerns" --argjson labels "$(jq -c '[.labels[].name]' <<< "$issued")" \
    --argjson number "$(jq .number <<< "$issued")" --argjson cutoff "$(jq -R -s -f "$root/.config/claims/cutoff.jq" "$root/.config/references/window.toml")" \
    -f "$root/.config/claims/unit.jq" \
  | jq -R -s -c 'split("\n") | map(select(length > 0))')
# A body that passes, on an open issue no flag or exemption marks, has no
# comment to write: a pass that took the flag off rewrote the comment then.
# So its comments are not read (#5078).
if [[ $(jq --argjson findings "$findings" '.state == "open" and ($findings | length) == 0
    and ([.labels[].name] | any(IN("status:unsectioned", "kind:epic", "collector")) | not)' <<< "$issued") == true ]]; then
  comments='[]'
else
  comments=$(gh api --paginate "repos/$repo/issues/$issue/comments?per_page=100" \
    --jq '.[] | select(.body | startswith("<!-- unit:check -->")) | {id, body}' | jq -s -c .)
fi
decision=$(jq -c --slurpfile findings <(printf '%s\n' "$findings") --slurpfile comments <(printf '%s\n' "$comments") \
  '{state, labels: [.labels[].name], findings: $findings[0], comments: $comments[0]}' <<< "$issued" \
  | jq -c -f "$here/unsectioned.jq")
case $(jq -r '.label // ""' <<< "$decision") in
  add) gh issue edit "$issue" --repo "$repo" --add-label status:unsectioned > /dev/null ;;
  remove) gh issue edit "$issue" --repo "$repo" --remove-label status:unsectioned > /dev/null ;;
esac
case $(jq -r '.comment.act // ""' <<< "$decision") in
  create) gh api -X POST "repos/$repo/issues/$issue/comments" -f body="$(jq -r .comment.body <<< "$decision")" > /dev/null ;;
  edit) gh api -X PATCH "repos/$repo/issues/comments/$(jq -r .comment.id <<< "$decision")" -f body="$(jq -r .comment.body <<< "$decision")" > /dev/null ;;
esac
printf '#%s: %s findings, label %s, comment %s\n' "$issue" "$(jq length <<< "$findings")" \
  "$(jq -r '.label // "kept"' <<< "$decision")" "$(jq -r '.comment.act // "kept"' <<< "$decision")"
