#!/usr/bin/env bash
# The cases of `check:ledger`'s issue reads (#4018). A scratch repository
# holds a ledger of two rows: `gap`, implemented with no witness and resting
# on #1, and `owing`, partial with its own exemplar owing on #2. For each
# case in `.config/ledger/cases.json` a stub `gh` answers the issues the case
# lists and fails every other read as a rate limit does. `check.bash` runs
# there, and its exit status and standard error are the case's.
set -euo pipefail
root=$PWD
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
repo="$scratch/repo"
mkdir -p "$repo/ledger" "$repo/crates/x" "$repo/corpus/ledger/features" "$scratch/gh" "$scratch/answers"
git init --quiet "$repo"
{
  awk '/^CREATE TABLE feature\(/,/\) WITHOUT ROWID;$/' ledger/features.sql
  echo "INSERT INTO feature VALUES('gap','workflow','A gap',NULL,'implemented','ordinary',NULL,'A row with no witness.','x',NULL,NULL,'#1',NULL);"
  echo "INSERT INTO feature VALUES('owing','workflow','An owing row',NULL,'partial','ordinary',NULL,'A partial row.','x',NULL,'corpus/ledger/features/owing.gandr','#2',NULL);"
} | sqlite3 -bail "$scratch/features.db"
sqlite3 "$scratch/features.db" .dump > "$repo/ledger/features.sql"
printf '%s\n' '/// `owing`' '/// Implemented: the row.' '/// Not implemented: the rest, #2.' 'package owing {}' \
  > "$repo/corpus/ledger/features/owing.gandr"
git -C "$repo" add .
printf '%s\n' '#!/usr/bin/env bash' \
  'if [[ "$1 $2" == "issue view" && -f $STUB_GH/$3 ]]; then cat "$STUB_GH/$3"; exit 0; fi' \
  'echo "HTTP 403: API rate limit exceeded" >&2' 'exit 1' > "$scratch/gh/gh"
chmod +x "$scratch/gh/gh"
failed=0
while IFS= read -r case; do
  rm -f "$scratch/answers"/*
  for number in $(jq -r '.answers | keys[]' <<< "$case"); do
    jq -r --arg n "$number" '.answers[$n]' <<< "$case" > "$scratch/answers/$number"
  done
  status=0
  (cd "$repo" && PATH="$scratch/gh:$PATH" STUB_GH="$scratch/answers" "$root/.config/ledger/check.bash") \
    > /dev/null 2> "$scratch/err" || status=$?
  if [[ $status != $(jq .exit <<< "$case") || $(< "$scratch/err") != $(jq -r .stderr <<< "$case") ]]; then
    printf 'ledger case FAILED: %s\n  exit %s, wanted %s\n  stderr:\n%s\n' \
      "$(jq -r .name <<< "$case")" "$status" "$(jq .exit <<< "$case")" "$(< "$scratch/err")" >&2
    failed=1
  fi
done < <(jq -c '.[]' .config/ledger/cases.json)
(( failed == 0 )) || exit 1
echo "ledger cases OK: $(jq length .config/ledger/cases.json) cases read their issues as recorded"
