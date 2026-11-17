#!/usr/bin/env bash
# Print the hosts block and page the fixer for a new red run (#6880).
#
#   hosts.bash              read the forge, print the block, page once
#   hosts.bash --dry-run    print the block and the pages, write nothing
#
# HOSTS_RUNS_FILE and HOSTS_RUNNERS_FILE name fixtures. The live task reads
# the forge into files and gives those files to jq. A large value is never
# a jq argument. RUNNERS_TOKEN is the App token that can list runners. The
# seat token cannot, and the counts then read unread.
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
dry=false
[[ ${1:-} == --dry-run ]] && dry=true
repo=${GH_REPO:-gandr-lang/gandr}
state=${HOSTS_STATE_DIR:-${XDG_STATE_HOME:-$HOME/.local/state}/gandr/hosts}
mkdir -p "$state"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
now=${HOSTS_NOW:-$(date -u +%s)}

if [[ -n ${HOSTS_RUNNERS_FILE:-} ]]; then
  cp "$HOSTS_RUNNERS_FILE" "$tmp/runners.json"
elif [[ -n ${RUNNERS_TOKEN:-} ]] && GH_TOKEN=$RUNNERS_TOKEN gh api "repos/$repo/actions/runners?per_page=100" > "$tmp/runners.json"; then
  :
else
  printf '%s\n' '{"runners":null}' > "$tmp/runners.json"
fi
if [[ -n ${HOSTS_RUNS_FILE:-} ]]; then
  cp "$HOSTS_RUNS_FILE" "$tmp/runs.json"
else
  gh api "repos/$repo/actions/runs?event=schedule&per_page=30" > "$tmp/runs.json" \
    || printf '%s\n' '{"workflow_runs":[]}' > "$tmp/runs.json"
fi
[[ -f $state/offline.json ]] || printf '%s\n' '{}' > "$state/offline.json"
printf '%s\n' "$now" > "$tmp/now.json"
jq -n --slurpfile runners "$tmp/runners.json" --slurpfile runs "$tmp/runs.json" \
  --slurpfile owners "$here/owners.json" --slurpfile offline "$state/offline.json" \
  --slurpfile now "$tmp/now.json" \
  '{runners: $runners[0].runners, runs: ($runs[0].workflow_runs // []), owners: $owners[0].owners, workflows: $owners[0].workflows, now: $now[0], offline: $offline[0]}' \
  > "$tmp/in.json"
jq -c -f "$here/hosts.jq" "$tmp/in.json" > "$tmp/out.json"
jq -r '.lines[]' "$tmp/out.json"
if [[ $dry == true ]]; then
  jq -r '.pages[].line' "$tmp/out.json"
  exit 0
fi
jq -c '.offline' "$tmp/out.json" > "$state/offline.json"
stamp=$state/pages
touch "$stamp"
page=${GANDR_PAGE:-}
if [[ -z $page && -x ${XDG_CONFIG_HOME:-$HOME/.config}/gandr/bin/page.sh ]]; then
  page=${XDG_CONFIG_HOME:-$HOME/.config}/gandr/bin/page.sh
fi
while IFS= read -r row; do
  [[ -n $row ]] || continue
  id=$(jq -r .run <<< "$row")
  line=$(jq -r .line <<< "$row")
  grep -qxF "$id" "$stamp" && continue
  if [[ -n $page ]]; then
    "$page" triage "$line" || echo "hosts: the page for $id did not arrive" >&2
  else
    echo "hosts: no pager, so this page is not sent: $line" >&2
  fi
  printf '%s\n' "$id" >> "$stamp"
done < <(jq -c '.pages[]' "$tmp/out.json")
