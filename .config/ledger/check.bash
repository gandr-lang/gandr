#!/usr/bin/env bash
# `check:ledger`: the features ledger (`ledger/features.sql`,
# `ledger/README.md`). The dump builds with every CHECK constraint holding (a
# refused row stops the build), re-dumps byte-identical, and every `parent`
# resolves. Every path a row names exists: a `crate` a directory under
# `crates/` or a `contrib/` path, a `corpus` entry a path from the root (a
# `::item` suffix naming a test inside it), an `exemplar` a file outside
# `pathological/`, which holds refusals. Every file under
# `corpus/ledger/features/` is named by a row. Every implemented or partial
# row outside the areas `exempt` lists, whose evidence is crate tests, names
# an exemplar. Every implemented or partial row naming neither a `corpus`
# witness nor an `exemplar` names in `issue` an open `kind:gap` issue, or a
# `kind:epic` of its steps (#2902), the issue stating what the witness still
# needs (#2526). A partial row whose exemplar is a source has its own,
# `corpus/ledger/features/<id>.gandr` (#2635), opening with a head of `///`
# lines: the row's `id`, a `/// Implemented:` line, and a
# `/// Not implemented:` line naming an open issue that owes the rest, or the
# comment shape's references line `/// - see: #n — not implemented: <what>`
# (crates/surface-corpus/README.md § Comments, #2918). The shared sources it
# was drawn from stay in `corpus`. Every finding is printed before the gate
# fails.
#
# The issues the rows rest on are read through `gh` in one GraphQL query of
# aliases, a hundred issues a request (#4263): a check that read each issue
# on its own made eighty-six requests, which with every seat's gates running
# tripped GitHub's per-minute limit. A failed read stops the check with the
# call and its error, never a verdict on a row (#4018): a rate limit or a
# network fault says nothing about the issue.
set -euo pipefail
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
db="$tmp/features.db"
sqlite3 -bail "$db" < ledger/features.sql
sqlite3 "$db" .dump > "$tmp/features.sql"
failed=0
if ! cmp -s "$tmp/features.sql" ledger/features.sql; then
  diff -u ledger/features.sql "$tmp/features.sql" >&2 || true
  echo 'ledger/features.sql is not its own re-dump; normalize it with `mise run ledger:build && mise run ledger:dump`' >&2
  failed=1
fi
if [ -n "$(sqlite3 "$db" 'PRAGMA foreign_key_check;')" ]; then
  sqlite3 "$db" "SELECT id || ': parent ' || parent || ' names no row' FROM feature WHERE parent NOT IN (SELECT id FROM feature);" >&2
  failed=1
fi
integrity=$(sqlite3 "$db" 'PRAGMA integrity_check;')
if [ "$integrity" != ok ]; then
  echo "$integrity" >&2
  failed=1
fi
while IFS='|' read -r id column paths; do
  for path in $paths; do
    case $column in
      crate) [[ -d crates/$path || ( $path == contrib/* && -e $path ) ]] ;;
      corpus) [[ -e ${path%%::*} || -e crates/surface-corpus/${path%%::*} ]] ;;
      exemplar) [[ $path == crate-tests || -f $path ]] ;;
    esac || { echo "$id: $column \`$path\` does not exist" >&2; failed=1; }
    if [[ $column == exemplar && $path == */pathological/* ]]; then
      echo "$id: exemplar \`$path\` shows a refusal; an exemplar is a model or strict program" >&2
      failed=1
    fi
  done
done < <(sqlite3 -separator '|' "$db" "
  SELECT id, 'crate', crate FROM feature WHERE crate IS NOT NULL
  UNION ALL SELECT id, 'corpus', corpus FROM feature WHERE corpus IS NOT NULL
  UNION ALL SELECT id, 'exemplar', exemplar FROM feature WHERE exemplar IS NOT NULL;")
sqlite3 "$db" "SELECT exemplar FROM feature WHERE exemplar IS NOT NULL;" | tr ' ' '\n' | sort -u > "$tmp/named"
git ls-files -- 'corpus/ledger/features/*.gandr' | sort > "$tmp/files"
while read -r file; do
  echo "$file: no row of the features ledger names it" >&2
  failed=1
done < <(comm -23 "$tmp/files" "$tmp/named")
exempt="'editor', 'workflow', 'storage', 'tooling', 'incremental', 'algorithms', 'machine', 'staging',
  'kernel', 'conversion', 'runtime', 'syntax', 'printing', 'diagnostics', 'rewriting', 'corpus'"
sqlite3 "$db" "
  SELECT id || ': an implemented or partial row in the language area ' || area || ' names no exemplar'
  FROM feature
  WHERE status IN ('implemented', 'partial') AND exemplar IS NULL AND area NOT IN ($exempt)
  ORDER BY id;" > "$tmp/unshown"
if [ -s "$tmp/unshown" ]; then
  cat "$tmp/unshown" >&2
  failed=1
fi
# Each issue's `<state>\t<gap>` once, `<gap>` whether it is a `kind:gap` or a
# `kind:epic`. Every number the rows name is gathered first and read in one
# query of aliases per hundred. A failed read prints the call and its error
# and stops the check: no row is judged on a state the check did not read.
declare -A issue=()
origin=$(git remote get-url origin 2> /dev/null || true)
repo=$(sed -nE 's#^(https://github\.com/|git@github\.com:)([^/]+/[^/.]+)(\.git)?$#\2#p' <<< "$origin")
repo=${repo:-gandr-lang/gandr}
read_issues() {
  local chunk=() n
  for n in "$@"; do
    chunk+=("$n")
    if (( ${#chunk[@]} == 100 )); then read_chunk "${chunk[@]}"; chunk=(); fi
  done
  (( ${#chunk[@]} == 0 )) || read_chunk "${chunk[@]}"
}
read_chunk() {
  local n query="{ repository(owner: \"${repo%/*}\", name: \"${repo#*/}\") { " out
  for n in "$@"; do query+="n$n: issue(number: $n) { state labels(first: 100) { nodes { name } } } "; done
  query+="} }"
  if ! out=$(gh api graphql -f query="$query" --jq '.data.repository | to_entries[] | [(.key | ltrimstr("n")), (.value.state // "MISSING"), ((.value.labels.nodes // []) | map(.name) | any(. == "kind:gap" or . == "kind:epic"))] | @tsv' 2> "$tmp/gh-error"); then
    printf '`gh api graphql` over %s failed, so no row is judged: %s\n' "$(printf '#%s ' "$@" | sed 's/ $//')" "$(paste -sd ' ' "$tmp/gh-error")" >&2
    echo 'ledger check FAILED' >&2
    exit 1
  fi
  while IFS=$'\t' read -r n state gap; do
    [[ -n $n ]] || continue
    issue[$n]="$state"$'\t'"$gap"
  done <<< "$out"
}
read_issue() {
  [[ -n ${issue[$1]:-} ]] && return
  printf '#%s was not among the issues read, so no row resting on it is judged\n' "$1" >&2
  echo 'ledger check FAILED' >&2
  exit 1
}
numbers=$({
  sqlite3 -separator '|' "$db" "
    SELECT coalesce(issue, '') FROM feature
    WHERE status IN ('implemented', 'partial') AND coalesce(corpus, '') = '' AND exemplar IS NULL;" \
    | grep -oE '(^| )#[0-9]+' || true
  while IFS='|' read -r id exemplar; do
    own=corpus/ledger/features/$id.gandr
    [[ $exemplar == "$own" && -f $own ]] || continue
    awk '/^\/\/\// { print; next } { exit }' "$own" \
      | grep -m1 -E '^/// (Not implemented: |- see: #[0-9]+ — not implemented: )' \
      | grep -oE '#[0-9]+' || true
  done < <(sqlite3 -separator '|' "$db" "
    SELECT id, exemplar FROM feature
    WHERE status = 'partial' AND exemplar IS NOT NULL;")
} | tr -d ' #' | grep -E '^[0-9]+$' | sort -un | tr '\n' ' ')
# shellcheck disable=SC2086
[[ -z $numbers ]] || read_issues $numbers
# A row with no witness rests on an open issue that builds it: a `kind:gap`,
# or a `kind:epic` of the steps, an epic being `kind:epic` alone (#2902).
while IFS='|' read -r id issues; do
  gap=
  for number in $(grep -oE '(^| )#[0-9]+' <<< "$issues" | tr -d ' #'); do
    read_issue "$number"
    if [[ ${issue[$number]} == $'OPEN\ttrue' ]]; then gap=$number; fi
  done
  if [[ -z $gap ]]; then
    echo "$id: an implemented or partial row naming no corpus witness and no exemplar names no open kind:gap or kind:epic issue (issue: ${issues:-none}); name a witness, or file the gap stating what it needs" >&2
    failed=1
  fi
done < <(sqlite3 -separator '|' "$db" "
  SELECT id, coalesce(issue, '') FROM feature
  WHERE status IN ('implemented', 'partial') AND coalesce(corpus, '') = '' AND exemplar IS NULL
  ORDER BY id;")
while IFS='|' read -r id exemplar; do
  own=corpus/ledger/features/$id.gandr
  if [[ $exemplar != "$own" ]]; then
    echo "$id: a partial row's exemplar is its own, \`$own\`, not \`$exemplar\`; state there what is and is not implemented (#2635)" >&2
    failed=1
    continue
  fi
  [[ -f $own ]] || continue
  head=$(awk '/^\/\/\// { print; next } { exit }' "$own")
  owed=$(grep -m1 -E '^/// (Not implemented: |- see: #[0-9]+ — not implemented: )' <<< "$head" || true)
  missing=()
  grep -qF "\`$id\`" <<< "$head" || missing+=("the row's id, \`$id\`")
  grep -q '^/// Implemented: ' <<< "$head" || missing+=('a `/// Implemented:` line')
  [[ -n $owed ]] || missing+=('a `/// Not implemented:` line or a `/// - see: #n — not implemented:` line')
  if [[ -n $owed ]]; then
    owing=
    for number in $(grep -oE '#[0-9]+' <<< "$owed" | tr -d '#'); do
      read_issue "$number"
      if [[ ${issue[$number]} == OPEN$'\t'* ]]; then owing=$number; break; fi
    done
    [[ -n $owing ]] || missing+=('an open issue on its not-implemented line that owes the rest')
  fi
  for lack in "${missing[@]}"; do
    printf '%s: the head of `%s` lacks %s (#2635)\n' "$id" "$own" "$lack" >&2
    failed=1
  done
done < <(sqlite3 -separator '|' "$db" "
  SELECT id, exemplar FROM feature
  WHERE status = 'partial' AND exemplar LIKE '%.gandr'
  ORDER BY id;")
if (( failed )); then
  echo 'ledger check FAILED' >&2
  exit 1
fi
echo "ledger check OK: $(sqlite3 "$db" 'SELECT count(*) FROM feature;') rows round-trip, every path exists, every exemplar is named, every language feature names one"
