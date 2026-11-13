#!/usr/bin/env bash
# The cases of the rows of the gates (#7021): each runs a gate's trap,
# `gate_exit` of `.config/mise/gate.bash`, in a scratch state directory, a
# scratch configuration directory and a scratch directory of host locks. It
# runs a pass, a failure, a stop, a `SIGTERM` and a check that a signal ends.
# It runs a host with a class and a host with none. It runs a gate beside
# another lane's gate for its whole run, and one beside a gate at its hold
# alone. It runs a heavy check alone. It then reads `report.jq` over a fixed
# set of rows.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
gate=$here/../mise/gate.bash
scratch=$(mktemp -d)
pids=()
trap 'kill "${pids[@]}" 2> /dev/null || :; rm -rf "$scratch"' EXIT
export XDG_STATE_HOME=$scratch/state XDG_CONFIG_HOME=$scratch/config GANDR_HOST_LOCK_DIR=$scratch/locks
unset GANDR_GATE_SLOT GANDR_GATE_BACKGROUND GATE_NO_WAIT MAKEFLAGS
rows=$XDG_STATE_HOME/gandr/gates.jsonl
mkdir -p "$XDG_CONFIG_HOME/gandr" "$GANDR_HOST_LOCK_DIR/gandr"
failed=0
cases=0

fail() {
  printf 'gate rows: %s\n' "$*" >&2
  failed=1
}

# Runs the script `$2` in a shell that sources the gate, with the rows
# emptied first; sets `status` to its exit status and `row` to the one row
# that it leaves, or to `none`. `$1` names the case.
run() {
  cases=$(( cases + 1 ))
  rm -f "$rows"
  status=0
  bash -c "set -euo pipefail; source \"\$1\"; $2" _ "$gate" > /dev/null 2>&1 || status=$?
  row=none
  if [[ -s $rows ]]; then
    if (( $(wc -l < "$rows") != 1 )); then fail "#7021: $1 leaves $(wc -l < "$rows" | tr -d ' ') rows, not 1"; fi
    row=$(< "$rows")
  fi
}

# Holds the row to the jq predicate `$2`; `$1` names the case.
holds() {
  if [[ $row == none ]] || ! jq -e "$2" > /dev/null <<< "$row"; then
    fail "#7021: $1: the row $row does not satisfy $2"
  fi
}

printf '{"class": "fast"}\n' > "$XDG_CONFIG_HOME/gandr/host.json"

run "a pass" 'gate_open check; gate_tree=abc; gate_ran=1'
[[ $status == 0 ]] || fail "#7021: a pass exits $status, not 0"
holds "a pass" '.gate == "check" and .result == "passed" and .status == 0 and .tree == "abc" and .held == null and .slot == null'
holds "a pass" '.host.class == "fast" and .host.arch != null and .host.cores > 0 and .seconds >= 0 and .end >= .start'
holds "a pass" '(.head | test("^[0-9a-f]{40}$")) and .wait == {lane: 0, slot: 0} and .beside == 0'

run "a failure" 'gate_open gate:all; false; gate_ran=1'
[[ $status == 1 ]] || fail "#7021: the trap changes the status of a failed gate to $status, not 1"
holds "a failure" '.gate == "gate:all" and .result == "failed" and .status == 1 and .tree == null'

run "a gate that ends with status 0 short of its end" 'gate_open check'
holds "a gate that ends with status 0 short of its end" '.result == "stopped" and .status == null'

cases=$(( cases + 1 ))
rm -f "$rows"
bash -c 'set -euo pipefail; source "$1"; gate_open check; sleep 30; gate_ran=1' _ "$gate" > /dev/null 2>&1 &
stopped=$!
for (( tries = 0; tries < 100; tries++ )); do
  pgrep -P "$stopped" sleep > /dev/null 2>&1 && break
  sleep 0.05
done
kill -TERM "$stopped"
status=0
wait "$stopped" || status=$?
[[ $status == 143 ]] || fail "#7021: a gate that SIGTERM ends exits $status, not 143"
row=none
[[ -s $rows ]] && row=$(< "$rows")
holds "a SIGTERM" '.result == "stopped" and .status == null'

run "a check that a signal ends" 'gate_open check; bash -c "kill -TERM \$\$"; gate_ran=1'
[[ $status == 143 ]] || fail "#7021: a gate whose check a signal ends exits $status, not 143"
holds "a check that a signal ends" '.result == "stopped" and .status == null'

rm "$XDG_CONFIG_HOME/gandr/host.json"
run "a host with no class" 'gate_open check; gate_ran=1'
holds "a host with no class" '.host.class == null'

# Another lane's gate holds its lane's lock beside this gate, and a third
# lane's lock keeps the record of a holder that has exited.
sleep 300 &
beside=$!
pids+=("$beside")
printf 'the other gate (pid %s, group %s, in /tmp, since 2026-01-01T00:00:00Z)\n' "$beside" "$beside" \
  > "$GANDR_HOST_LOCK_DIR/gandr/gate-lane-other.1.lock"
(exit 0) &
gone=$!
wait "$gone"
printf 'a gone gate (pid %s, group %s, in /tmp, since 2026-01-01T00:00:00Z)\n' "$gone" "$gone" \
  > "$GANDR_HOST_LOCK_DIR/gandr/gate-lane-gone.1.lock"
run "a gate beside another" 'gate_open check; GANDR_GATE_SLOTS=1 GATE_NO_WAIT=1; gate_slots=1; hold_gate_slot "the gate of a case"; gate_ran=1'
[[ $status == 0 ]] || fail "#7021: a gate that holds a slot exits $status, not 0"
holds "a gate beside another" '.beside == 1 and .slot == 1 and .held != null and .held >= .start and .end >= .held'
status=0
(GANDR_GATE_SLOTS=1 GATE_NO_WAIT=1 bash -c 'source "$1"; hold_gate_slot taker' _ "$gate") > /dev/null 2>&1 || status=$?
[[ $status == 0 ]] || fail "#7021: the trap leaves the slot of the gate held: exit $status"

# A gate beside that starts after this gate opens and ends before this gate
# ends: only the count at the hold of the slot reads it.
rm "$GANDR_HOST_LOCK_DIR/gandr/gate-lane-other.1.lock"
run "a gate beside at the hold alone" 'gate_open check; sleep 300 & brief=$!; printf "a brief gate (pid %s, group %s, in /tmp, since 2026-01-01T00:00:00Z)\n" "$brief" "$brief" > "$GANDR_HOST_LOCK_DIR/gandr/gate-lane-brief.1.lock"; GATE_NO_WAIT=1; gate_slots=1; hold_gate_slot "the gate of a case"; kill "$brief"; wait "$brief" || :; gate_ran=1'
holds "a gate beside at the hold alone" '.beside == 1'

run "a heavy check run alone" 'GATE_NO_WAIT=1; gate_slots=1; hold_gate_slot "a heavy check alone"'
[[ $row == none ]] || fail "#7021: a heavy check run alone leaves the row $row"

# The report over fixed rows: four passes of `check` on one class, one pass
# before the window, one failure, and a torn line.
cases=$(( cases + 1 ))
day=2026-11-10
from=$(jq -n --arg day "$day" '($day + "T00:00:00Z" | fromdateiso8601) * 1000000')
{
  for seconds in 300 100 400 200; do
    jq -n -c --argjson start "$from" --argjson seconds "$seconds" \
      '{gate: "check", start: ($start + 1000000), seconds: $seconds, result: "passed", host: {arch: "aarch64", class: "fast", cores: 16}}'
  done
  jq -n -c --argjson start "$from" '{gate: "check", start: ($start - 1), seconds: 9000, result: "passed", host: {arch: "aarch64", class: "fast", cores: 16}}'
  jq -n -c --argjson start "$from" '{gate: "check", start: ($start + 5), seconds: 7, result: "failed", host: {arch: "aarch64", class: null, cores: 16}}'
  printf '{"gate": "check", "sta\n'
} > "$scratch/fixed.jsonl"
report=$(jq -R -n -r --arg since "$day" --arg file fixed -f "$here/report.jq" "$scratch/fixed.jsonl")
expected="5 rows of 6 since $day in fixed; 1 lines skipped

|gate|class|arch|result|runs|p50 s|p90 s|
|---|---|---|---|---|---|---|
|check|none|aarch64|failed|1|7|7|
|check|fast|aarch64|passed|4|250|400|"
[[ $report == "$expected" ]] || fail "#7021: the report over the fixed rows reads:
$report
not:
$expected"

(( failed == 0 )) || exit 1
echo "gate rows OK: $cases cases: a pass, a failure, a stop, a SIGTERM, a signal to a check, a class, two gates beside, a heavy check alone and the report"
