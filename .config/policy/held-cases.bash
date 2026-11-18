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

fail() {
  echo "held case FAILED: $1"
  echo "  got: $2"
  failed=1
}

# The record line of the function `$1` with the body `$2`, of the kind `$3`.
item() {
  printf '{"record":"item","path":"case::%s","kind":"%s","body":"%s"}\n' "$1" "${3:-fn}" "$2"
}

# The line that `held.bash` prints for the case directory `$1`: the base
# record `$3` and the head record `$4` of the unit file `$2`, against the base
# `$5`.
held_of() {
  local name=$1 unit=$2 base=$3 head=$4 commit=$5
  mkdir -p "$scratch/$name/base" "$scratch/$name/records"
  printf '%s' "$base" > "$scratch/$name/base/$unit"
  printf '%s' "$head" > "$scratch/$name/records/$unit"
  "$here/held.bash" "$scratch/$name/base" "$scratch/$name/records" "$commit"
}

# The exit status and the output of `group-base.bash` under the event `$1` and
# the base `$2`.
stop_of() {
  local status=0 got
  got=$(env GITHUB_EVENT_NAME="$1" GATE_BASE="$2" "$here/group-base.bash" 2>&1) || status=$?
  echo "exit $status: $got"
}

commit=01c2f5b13c6ca6b789ab13f12cc7d261b2374dbd
line="held: against the base 01c2f5b13c6c, allocation_free_region holds"

got=$(held_of new unit.lib.jsonl '' "$(item a aaaa1111-01; item b aaaa1111-02)" "$commit")
[[ $got == "$line 2 changed functions in 1 units" ]] \
  || fail "#7632: a unit new at the base holds each function" "$got"
got=$(held_of changed unit.lib.jsonl "$(item a aaaa1111-01; item b aaaa1111-02)" \
  "$(item a aaaa1111-01; item b aaaa1111-09; item c aaaa1111-03 assoc-fn; item d aaaa1111-04 closure; echo 'no JSON')" "$commit")
[[ $got == "$line 2 changed functions in 1 units" ]] \
  || fail "#7632: a changed body and a new path are held, a kept body and a closure are not" "$got"
got=$(held_of scheme unit.lib.jsonl "$(item a bbbb2222-01)" "$(item a aaaa1111-05)" "$commit")
[[ $got == "$line 0 changed functions in 0 units" ]] \
  || fail "#7632: a base of another scheme holds nothing" "$got"
got=$(held_of test unit.test.jsonl "$(item a aaaa1111-01)" "$(item a aaaa1111-02)" "$commit")
[[ $got == "$line 0 changed functions in 0 units" ]] \
  || fail "#7632: a test unit is not counted" "$got"
got=$(held_of none unit.lib.jsonl "$(item a aaaa1111-01)" "$(item a aaaa1111-02)" "")
[[ $got == "held: no GATE_BASE names a base, so allocation_free_region holds the crates of its default alone" ]] \
  || fail "#7632: no base holds the crates of the default alone" "$got"

got=$(stop_of merge_group "")
[[ $got == "exit 1: "*"(#7632)" ]] \
  || fail "#7632: a merge group with no base stops by name" "$got"
got=$(stop_of merge_group "$commit")
[[ $got == "exit 0: " ]] \
  || fail "#7632: a merge group with its base goes on" "$got"
got=$(stop_of "" "")
[[ $got == "exit 0: " ]] \
  || fail "#7632: a run outside a merge group with no base goes on" "$got"

(( failed == 0 )) || exit 1
echo "held case OK: the count holds a new unit, a changed body and a new path, and leaves a kept body, another scheme and a test unit; a merge group with no base stops by name"
