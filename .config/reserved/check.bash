#!/usr/bin/env bash
# The tests that are wide by design (#7539), run by `check:reserved-width` as
# `check.bash <nextest config> <root>...`. A test in a `tests/` directory under
# a root that asks for `Width::Reserved` in its body takes the host's width. So
# a `threads-required` override of the config names it, and nextest runs
# nothing beside it. nextest passes no `threads-required` to a test, so each
# side states the fact once, and the check refuses a test on one side alone.
# The check reads the names from the override's `test(=NAME)` terms, so it
# refuses a term of another form.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
config=$1
shift
asked=$(
  while IFS= read -r -d '' file; do
    awk -f "$here/requests.awk" "$file"
  done < <(find "$@" -path '*/tests/*' -name '*.rs' -print0) | sort -u
)
filters=$(yq -p toml -o json -I 0 '[.profile[]?.overrides[]? | select(has("threads-required")) | .filter // ""]' "$config")
terms=$(jq -r '.[] | split(" or ")[] | gsub("^\\s+|\\s+$"; "")' <<< "$filters")
failed=0
named=()
while IFS= read -r term; do
  [[ -n $term ]] || continue
  if [[ $term =~ ^test\(=([A-Za-z0-9_:]+)\)$ ]]; then
    named+=("${BASH_REMATCH[1]##*::}")
  else
    echo "check:reserved-width: the term \`$term\` of a \`threads-required\` override in $config is not \`test(=NAME)\`" >&2
    failed=1
  fi
done <<< "$terms"
reserved=$(printf '%s\n' "${named[@]}" | awk 'NF' | sort -u)
requested=$(awk -F '\t' 'NF { print $2 }' <<< "$asked" | sort -u)
while IFS= read -r test; do
  [[ -n $test ]] || continue
  file=$(awk -F '\t' -v test="$test" '$2 == test { print $1; exit }' <<< "$asked")
  echo "check:reserved-width: \`$test\` in $file asks for \`Width::Reserved\`, and no \`threads-required\` override in $config names it" >&2
  failed=1
done < <(comm -23 <(printf '%s\n' "$requested") <(printf '%s\n' "$reserved"))
while IFS= read -r test; do
  [[ -n $test ]] || continue
  echo "check:reserved-width: a \`threads-required\` override in $config names \`$test\`, and no test of a \`tests/\` directory asks for \`Width::Reserved\` in its body" >&2
  failed=1
done < <(comm -13 <(printf '%s\n' "$requested") <(printf '%s\n' "$reserved"))
(( failed == 0 )) || exit 1
echo "reserved-width check OK: $(awk 'NF' <<< "$requested" | wc -l) tests ask for Width::Reserved, and a threads-required override names each of them"
