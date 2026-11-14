#!/usr/bin/env bash
# The count that `held.bash` gives is the set that `allocation_free_region`
# holds (#7632). `check:dylint` runs the cases after its own run. Each case
# writes a base record and a head record of one unit to a scratch directory,
# and reads the line that `held.bash` prints. The bodies carry the scheme
# `aaaa1111`, as the lint's records carry its own.
# The stop of `group-base.bash` ends a merge group that names no base, and
# lets each other run go on.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
failed=0

# The record line of the function `$1` with the body `$2`, of the kind `$3`.
item() {
  printf '{"record":"item","path":"case::%s","kind":"%s","body":"%s"}\n' "$1" "${3:-fn}" "$2"
}

# Runs the case `$1`: its base record `$3` and its head record `$4` of the unit
# file `$2`, against the base `$5`. Fails when the line is not `$6`.
case_of() {
  local name=$1 unit=$2 base=$3 head=$4 commit=$5 want=$6 got
  mkdir -p "$scratch/$name/base" "$scratch/$name/records"
  printf '%s' "$base" > "$scratch/$name/base/$unit"
  printf '%s' "$head" > "$scratch/$name/records/$unit"
  got=$("$here/held.bash" "$scratch/$name/base" "$scratch/$name/records" "$commit")
  if [[ $got != "$want" ]]; then
    echo "held case FAILED: $name"
    echo "  want: $want"
    echo "  got:  $got"
    failed=1
  fi
}

commit=01c2f5b13c6ca6b789ab13f12cc7d261b2374dbd
case_of "#7632: a unit new at the base holds each function" unit.lib.jsonl \
  '' "$(item a aaaa1111-01; item b aaaa1111-02)" "$commit" \
  "held: against the base 01c2f5b13c6c, allocation_free_region holds 2 changed functions in 1 units"
case_of "#7632: a changed body and a new path are held, a kept body and a closure are not" unit.lib.jsonl \
  "$(item a aaaa1111-01; item b aaaa1111-02)" \
  "$(item a aaaa1111-01; item b aaaa1111-09; item c aaaa1111-03 assoc-fn; item d aaaa1111-04 closure; echo 'no JSON')" "$commit" \
  "held: against the base 01c2f5b13c6c, allocation_free_region holds 2 changed functions in 1 units"
case_of "#7632: a base of another scheme holds nothing" unit.lib.jsonl \
  "$(item a bbbb2222-01)" "$(item a aaaa1111-05)" "$commit" \
  "held: against the base 01c2f5b13c6c, allocation_free_region holds 0 changed functions in 0 units"
case_of "#7632: a test unit is not counted" unit.test.jsonl \
  "$(item a aaaa1111-01)" "$(item a aaaa1111-02)" "$commit" \
  "held: against the base 01c2f5b13c6c, allocation_free_region holds 0 changed functions in 0 units"
case_of "#7632: no base holds the crates of the default alone" unit.lib.jsonl \
  "$(item a aaaa1111-01)" "$(item a aaaa1111-02)" "" \
  "held: no GATE_BASE names a base, so allocation_free_region holds the crates of its default alone"

# Runs `group-base.bash` under the event `$2` and the base `$3`. Fails the case
# `$1` when the exit status is not `$4`, or when the stop does not name #7632.
stop_of() {
  local name=$1 event=$2 base=$3 want=$4 status=0 got
  got=$(env GITHUB_EVENT_NAME="$event" GATE_BASE="$base" "$here/group-base.bash" 2>&1) || status=$?
  if [[ $status != "$want" || ( $want == 1 && $got != *"(#7632)"* ) ]]; then
    echo "held case FAILED: $name"
    echo "  want: exit $want"
    echo "  got:  exit $status: $got"
    failed=1
  fi
}

stop_of "#7632: a merge group with no base stops by name" merge_group "" 1
stop_of "#7632: a merge group with its base goes on" merge_group "$commit" 0
stop_of "#7632: a run outside a merge group with no base goes on" "" "" 0

(( failed == 0 )) || exit 1
echo "held case OK: the count holds a new unit, a changed body and a new path, and leaves a kept body, another scheme and a test unit; a merge group with no base stops by name"
