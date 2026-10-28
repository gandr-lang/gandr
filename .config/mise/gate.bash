# The gate graph's host-wide slot (#3057), sourced by `check`. Three seats'
# gates on one host pushed its load past 50 on 32 cores, and the enforcing
# suite's slowest tests, which pass alone in 9 to 11 seconds, timed out at 30:
# a false red that costs a rerun and hides a real one. So `mise run check`
# holds one of `GANDR_GATE_SLOTS` (default 2) slots for its whole run. Its two
# test suites, `check:tests` and `check:tests-enforcing`, run at once, so each
# takes the host's cores divided by the slots and by the two suites, never
# more. A `check:*` task run alone takes no slot.
#
# A slot is the host lock `gate` (`host-lock.bash`, #3105): `gate.<n>.lock`
# under `gandr/` in the user's runtime directory, held with `flock(2)` for the
# gate and everything it started. With every slot held, the gate prints
# `gate: waiting on <holders>` and tries again every 5 seconds; with
# `GATE_NO_WAIT=1`, which `check --no-wait` sets, it refuses at once, naming
# them.

source "${BASH_SOURCE[0]%/*}/host-lock.bash"

gate_slots=${GANDR_GATE_SLOTS:-2}

# Takes a free slot, waiting for one unless `GATE_NO_WAIT=1`, and records the
# holder as `$*`; sets `gate_slot` to its number.
hold_gate_slot() {
  [[ $gate_slots =~ ^[1-9][0-9]*$ ]] || { echo "check: GANDR_GATE_SLOTS is \`$gate_slots\`, not a count of slots" >&2; exit 2; }
  if [[ ${GATE_NO_WAIT:-} == 1 ]]; then
    host_lock --no-wait gate "$gate_slots" "$@"
  else
    host_lock gate "$gate_slots" "$@"
  fi
  gate_slot=$host_slot
}

# The test threads each of a gate's two suites takes: the host's cores
# divided by the slots and by the suites, at least one, and never more than a
# `NEXTEST_TEST_THREADS` already set.
gate_threads() {
  local cores share
  cores=$(getconf _NPROCESSORS_ONLN)
  share=$(( cores / gate_slots / 2 ))
  (( share >= 1 )) || share=1
  if [[ ${NEXTEST_TEST_THREADS:-} =~ ^[1-9][0-9]*$ ]] && (( NEXTEST_TEST_THREADS < share )); then
    share=$NEXTEST_TEST_THREADS
  fi
  printf '%s\n' "$share"
}
