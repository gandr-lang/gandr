# The issues the features ledger rests on as owing work: the ones
# `check:ledger` reads through `gh` and refuses once none of a row's is open
# (#2526, #2635). One `<row>\t<n> <n> ...` line per row, from the built
# database `$1`:
#
# - an implemented or partial row naming no corpus witness and no exemplar:
#   the issues its `issue` column names;
# - a partial row whose exemplar is its own source: the issues the
#   `/// Not implemented:` line of that source's head names.
#
# `report:deps` reads them so a closed or closing issue a row still owes on
# is seen (#2973).
ledger_owing() {
  local db=$1 id issues exemplar
  while IFS='|' read -r id issues; do
    printf '%s\t%s\n' "$id" "$(grep -oE '#[0-9]+' <<< "$issues" | tr -d '#' | paste -sd ' ')"
  done < <(sqlite3 -separator '|' "$db" "
    SELECT id, coalesce(issue, '') FROM feature
    WHERE status IN ('implemented', 'partial') AND coalesce(corpus, '') = '' AND exemplar IS NULL
    ORDER BY id;")
  while IFS='|' read -r id exemplar; do
    [[ $exemplar == "corpus/ledger/features/$id.gandr" && -f $exemplar ]] || continue
    printf '%s\t%s\n' "$id" "$(awk '/^\/\/\// { print; next } { exit }' "$exemplar" \
      | awk '/^\/\/\/ Not implemented: / { print; exit }' | grep -oE '#[0-9]+' | tr -d '#' | paste -sd ' ')"
  done < <(sqlite3 -separator '|' "$db" "
    SELECT id, exemplar FROM feature
    WHERE status = 'partial' AND exemplar LIKE '%.gandr'
    ORDER BY id;")
}
