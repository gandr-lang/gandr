#!/usr/bin/env bash
# The rows a replay makes due (#6144, `due.jq`), run by `check:replay`. Each
# case of `cases.json` gives the paths the base moved, the paths the own
# commits change and the crates, and names the rows the rule makes due, read
# against the committed `artifacts.json`.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
failed=0
count=0
while IFS= read -r case; do
  count=$((count + 1))
  name=$(jq -r .name <<< "$case")
  want=$(jq -c '.due | sort' <<< "$case")
  got=$(jq -c --slurpfile rows "$here/artifacts.json" '{rows: $rows[0], moved, own, crates}' <<< "$case" \
    | jq -c -f "$here/due.jq" | jq -c 'map(.name) | sort')
  if [[ $got != "$want" ]]; then
    echo "replay case FAILED: $name: due $got, recorded $want" >&2
    failed=1
  fi
done < <(jq -c '.[]' "$here/cases.json")
(( failed == 0 )) || exit 1
echo "replay cases OK: $count cases make due the rows recorded"
