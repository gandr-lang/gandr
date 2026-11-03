#!/usr/bin/env bash
# The test groups the CI profiles put heavy tests in (#4846), run by
# `check:test-groups` over the cases in `walks.json`. Each case names a
# profile, a package, a group, its widest thread count and the tests measured
# heavy enough to need it. nextest resolves the profile's groups over the
# package's built tests (`show-config test-groups`), and the case passes when
# the group takes at most `max_threads` threads and holds every named test.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
cases=$here/walks.json
failed=0

count=$(jq length "$cases")
for (( i = 0; i < count; i++ )); do
  name=$(jq -r ".[$i].name" "$cases")
  shown=$(cargo nextest show-config test-groups --no-pager --color never \
    --profile "$(jq -r ".[$i].profile" "$cases")" --package "$(jq -r ".[$i].package" "$cases")" \
    --locked --config 'resolver.feature-unification="workspace"' --cargo-quiet --cargo-quiet)
  shown=$(awk -v group="$(jq -r ".[$i].group" "$cases")" '$1 == "group:" {held = ($2 == group)} held' <<< "$shown")
  threads=$(awk -v group="$(jq -r ".[$i].group" "$cases")" '$1 == "group:" && $2 == group {gsub(/[^0-9]/, "", $NF); print $NF}' <<< "$shown")
  missing=$(jq -r ".[$i].tests[]" "$cases" | while read -r test; do
    awk -v test="$test" '$1 == test {found = 1} END {exit !found}' <<< "$shown" || echo "$test"
  done)
  if [[ -z $threads ]] || (( threads > $(jq -r ".[$i].max_threads" "$cases") )) || [[ -n $missing ]]; then
    printf 'test-groups case %s\n  threads: %s\n  missing: %s\n' "$name" "${threads:-no group}" "$(paste -sd ' ' <<< "$missing")" >&2
    failed=1
  fi
done
(( failed == 0 )) || exit 1
echo "test-groups OK: $count cases hold their heavy tests at their widths"
