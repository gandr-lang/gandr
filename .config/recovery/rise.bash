#!/usr/bin/env bash
# The rise of a recovery row against the change's base (#6806), run by
# `check:recovery-rise`. `rise.bash <base>` reads each recovery record that
# the change from `<base>` to HEAD modifies, and compares its rows with the
# record at the base. A re-record (`corpus:goldens`, `UPDATE_EXPECT`) takes
# every row as the truth, so a dropped row whose obligations rise passes the
# sweep. This check refuses such a row unless `tests/recovery-owed.tsv` names
# its source and its token with the issue that owes the lost count (#6323).
#
# A record whose source the change edits, or whose row count changes, holds
# other tokens, so its rows do not compare one to one, and it is read as a
# tree change. A row whose obligations fall passes, and so does a row whose
# nodes alone change. A whole or cut-short row that moves is a tree change,
# which the sweep reads. The sweep itself refuses an owed line whose row
# recovers, so a list never outlives its change.
#
# Each refusal is one line: the source, the token, the obligations before
# and after, and the rise. The run exits 1 when it prints one.
set -euo pipefail
base=${1:?usage: rise.bash <base>}
if ! git rev-parse --verify --quiet "$base^{commit}" > /dev/null; then
  echo "recovery-rise: the base $base does not read; fetch it" >&2
  exit 2
fi
records=crates/surface-parser/tests/recovery/
owed=crates/surface-parser/tests/recovery-owed.tsv
# A tree from before #6323 holds no owed file, so it lists no row.
[[ -f $owed ]] || owed=/dev/null
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
# The sources that the change edits, by their names in the sweep.
git diff --no-renames --name-only "$base" HEAD -- corpus crates/surface-corpus/strict \
  | awk '/^corpus\// { sub(/^corpus\//, "fixture/"); print; next }
         /^crates\/surface-corpus\/strict\// { sub(/^crates\/surface-corpus\/strict\//, "strict/"); print }' \
  > "$scratch/edited"
refused=0
while IFS= read -r path; do
  name=${path#"$records"}
  name=${name%.recovery}.gandr
  if grep -qxF -- "$name" "$scratch/edited"; then continue; fi
  git show "$base:$path" > "$scratch/before"
  git show "HEAD:$path" > "$scratch/after"
  if [[ $(wc -l < "$scratch/before") != $(wc -l < "$scratch/after") ]]; then continue; fi
  if ! awk -F'\t' -v name="$name" '
      FILENAME == ARGV[1] { if ($0 !~ /^#/ && NF >= 4 && $1 == name) owed[$2] = $4; next }
      FILENAME == ARGV[2] { if ($1 == "T") before[FNR] = $5; next }
      $1 == "T" && (FNR in before) && $5 + 0 > before[FNR] + 0 {
        token = FNR - 2
        if (token in owed) next
        printf "recovery-rise: %s drop %d: obligations %d -> %d, a rise of %d; list it in tests/recovery-owed.tsv with the issue that owes %d, or repair it (#6806)\n", name, token, before[FNR], $5, $5 - before[FNR], before[FNR]
        rose = 1
      }
      END { exit rose }
    ' "$owed" "$scratch/before" "$scratch/after"; then
    refused=1
  fi
done < <(git diff --no-renames --name-only --diff-filter=M "$base" HEAD -- "$records")
exit "$refused"
