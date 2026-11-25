#!/usr/bin/env bash
# The cases of the differential's comparison (#7286): what a width keeps of
# the serial run, as the ruling on #7286 sets it.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
# shellcheck source=differential.bash
source "$here/differential.bash"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
cases=0
fail() {
  printf 'differential cases FAILED: %s\n' "$1" >&2
  exit 1
}
# Write the lines of run `$1` from the remaining arguments, one line each.
run() {
  local name=$1
  shift
  printf '%s\n' "$@" | differential_lines > "$scratch/$name"
}
# The comparison of the width with the serial run admits it (`kept`) or
# refuses it (`departs`).
check() {
  local reading=$1 want=$2
  cases=$((cases + 1))
  if differential_compare "$scratch/serial" "$scratch/wide" > "$scratch/why"; then
    [[ $want == kept ]] || fail "$reading: the comparison admits the width"
  else
    [[ $want == departs ]] || fail "$reading: the comparison refuses the width: $(< "$scratch/why")"
    [[ -s $scratch/why ]] || fail "$reading: the refusal names no line"
  fi
}
line='measure: a.gandr: f: 38 bytes, 6 shared, 12 unshared'
summary='sources: 1 read (1 strict, 0 fixture, 0 pending), 0 refused as a whole, 0 no longer pending, 0 faulted'
run serial "$line, 6 expanded, 0 recalled, 3 kept, 1200 ns" 'schedule: a.gandr: 1 jobs, serial 1200 ns' \
  'speculation: a.gandr: rank off; 0 rollbacks' "$summary"
run wide "$line, 6 expanded, 0 recalled, 3 kept, 900 ns" 'schedule: a.gandr: 1 jobs, serial 900 ns' \
  'speculation: a.gandr: rank on; 0 rollbacks' "$summary"
check "a width that differs in its times, its schedule and its group" kept
run wide "$line, 8 expanded, 2 recalled, 1 kept, untimed" "$summary"
check "a census that expands more and keeps less" kept
run wide "$line, 5 expanded, 0 recalled, 3 kept, 900 ns" "$summary"
check "a census that expands less than the serial run" departs
run wide 'measure: a.gandr: f: 38 bytes, 7 shared, 12 unshared, 6 expanded, 0 recalled, 3 kept, 900 ns' "$summary"
check "another shared count" departs
run wide 'measure: a.gandr: f: 38 bytes, 6 shared, 13 unshared, 6 expanded, 0 recalled, 3 kept, 900 ns' "$summary"
check "another unshared count" departs
run wide "$line, admitted on a recorded verdict, 900 ns" "$summary"
check "a declaration admitted on a recorded verdict in place of a check" departs
run wide "$line, 6 expanded, 0 recalled, 3 kept, 900 ns" \
  'sources: 1 read (1 strict, 0 fixture, 0 pending), 1 refused as a whole, 0 no longer pending, 0 faulted'
check "another verdict in the summary" departs
run wide "$summary"
check "a declaration that does not cross into the kernel" departs
run wide "$line, 6 expanded, 0 recalled, 3 kept, 900 ns"
check "a run that ends before the summary" departs
echo "differential cases OK: $cases cases read the times, the schedule and the group as free, the census as a bound and each other line as exact"
