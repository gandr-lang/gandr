#!/usr/bin/env bash
# The cases of `.config/vscode-smoke/admits.bash` (#3696), each in
# `.config/vscode-smoke/cases.json`: the rule runs with the case's kernel and
# with only the case's variables beside `PATH`, and its exit is compared with
# `admitted`.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
failed=0
while IFS= read -r case; do
  name=$(jq -r .name <<< "$case")
  mapfile -t vars < <(jq -r '.env | to_entries[] | "\(.key)=\(.value)"' <<< "$case")
  admitted=false
  if env -i PATH="$PATH" "${vars[@]}" "$here/admits.bash" "$(jq -r .kernel <<< "$case")"; then admitted=true; fi
  if [[ $admitted != $(jq -r .admitted <<< "$case") ]]; then
    printf 'vscode smoke admission case FAILED: %s\n  admitted: %s\n' "$name" "$admitted" >&2
    failed=1
  fi
done < <(jq -c '.[]' "$here/cases.json")
(( failed == 0 )) || exit 1
echo "vscode smoke admission check OK: $(jq length "$here/cases.json") cases admitted as recorded"
