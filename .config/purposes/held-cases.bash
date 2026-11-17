#!/usr/bin/env bash
# The cases of `.config/purposes/findings.sql` on the systems that hold an
# entry (#7674). Each case builds a ledger from the schema of
# `ledger/purposes.sql` and `ledger/concerns.sql`, with its own rows, entries
# and host system, and compares the findings with the lines it states. It
# prints each failing case and exits 1 on any failure.
set -euo pipefail
root=$(git rev-parse --show-toplevel)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
failed=0
row="INSERT INTO purpose VALUES('surface-dispatcher','pool::ring::with_ring','function','Runs a work on the thread''s ring.',NULL,'fits','sound',NULL);"
other="INSERT INTO purpose VALUES('surface-dispatcher','pool::Pool','struct','Holds the workers.',NULL,'fits','sound',NULL);"
linux="INSERT INTO held_by VALUES('surface-dispatcher','pool::ring::with_ring','function','linux');"
pool=$'surface-dispatcher\tpool::Pool\tstruct\tsrc/pool.rs:1'
ring=$'surface-dispatcher\tpool::ring::with_ring\tfunction\tsrc/pool/ring.rs:44'
none="surface-dispatcher::pool::ring::with_ring (function): a row naming no entry of \`mise run purposes:list surface-dispatcher\`; correct its path or kind, or delete it"
elsewhere="surface-dispatcher::pool::ring::with_ring (function, src/pool/ring.rs:44): listed on darwin, and its held_by rows name other systems alone; add INSERT INTO held_by VALUES('surface-dispatcher','pool::ring::with_ring','function','darwin'); to ledger/purposes.sql, or delete its held_by rows"
orphan="surface-dispatcher::pool::ring::with_ring (function): a held_by row for linux with no purpose row; add its purpose row, or delete it"
fail() {
  printf 'purposes held case %s\n' "$1" >&2
  failed=1
}
# findings <name> <system> <rows> <entries> <expected findings>: the findings
# equal the expected lines, or the difference goes to standard error.
findings() {
  local name=$1 system=$2 rows=$3 entries=$4 expected=$5 db="$scratch/$1.db" found
  {
    awk '/^INSERT INTO /{next} {print}' "$root/ledger/purposes.sql"
    echo "$rows"
  } | sqlite3 -bail "$db"
  sqlite3 -bail "$db" < "$root/ledger/concerns.sql"
  printf '%s\n' "$entries" | awk 'NF' > "$scratch/$name.tsv"
  sqlite3 -bail -tabs "$db" 'CREATE TABLE entry(crate TEXT, path TEXT, kind TEXT, location TEXT);' ".import $scratch/$name.tsv entry" \
    'CREATE TABLE checked(crate TEXT);' "INSERT INTO checked VALUES('surface-dispatcher');" \
    'CREATE TABLE host(system TEXT);' "INSERT INTO host VALUES('$system');"
  found=$(sqlite3 -bail "$db" < "$root/.config/purposes/findings.sql")
  [[ $found == "$expected" ]] && return 0
  printf 'expected\n%s\nfound\n%s\n' "$expected" "$found" >&2
  return 1
}
findings darwin-reads-no-linux-row darwin "$other$row$linux" "$pool" '' \
  || fail "#7674: on darwin, the row of an entry that held_by names on linux alone gives no finding"
findings linux-reads-its-row linux "$other$row$linux" "$pool" "$none" \
  || fail "#7674: on linux, the row of a linux entry with no listed entry is a finding"
findings unheld-row-reads-everywhere darwin "$other$row" "$pool" "$none" \
  || fail "#7674: a row with no held_by row reads against the listing of each system"
findings listed-on-a-left-out-system darwin "$other$row$linux" "$pool"$'\n'"$ring" "$elsewhere" \
  || fail "#7674: an entry listed on a system that its held_by rows leave out is a finding"
findings held-row-without-purpose linux "$other$linux" "$pool" "$orphan" \
  || fail "#7674: a held_by row with no purpose row is a finding"
findings linux-row-with-its-entry linux "$other$row$linux" "$pool"$'\n'"$ring" '' \
  || fail "#7674: on linux, the row of a linux entry that the listing holds gives no finding"
if (( failed )); then
  exit 1
fi
echo 'purposes held cases OK: 6 cases give their findings'
