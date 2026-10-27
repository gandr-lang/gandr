# The gate graph's host-wide slot (#3057), sourced by `check`. Three seats'
# gates on one host pushed its load past 50 on 32 cores, and the enforcing
# suite's slowest tests, which pass alone in 9 to 11 seconds, timed out at 30:
# a false red that costs a rerun and hides a real one. So `mise run check`
# holds one of `GANDR_GATE_SLOTS` (default 2) slots for its whole run. Its two
# test suites, `check:tests` and `check:tests-enforcing`, run at once, so each
# takes the host's cores divided by the slots and by the two suites, never
# more. A `check:*` task run alone takes no slot.
#
# A slot is `gate.<n>.lock` under `gandr/` in the user's runtime directory
# (`mutants_lock_dir`), locked exclusively with `flock(2)` on file descriptor
# 9, as `mutants.bash` locks the mutation run, so the lock belongs to the gate
# and everything it started, and a killed gate never leaves it held. The file
# names its holder (the command, its pid, worktree and start). With every slot
# held, the gate prints `check: waiting on <holders>` and tries again every 5
# seconds; with `GATE_NO_WAIT=1`, which `check --no-wait` sets, it refuses at
# once, naming them.

source "${BASH_SOURCE[0]%/*}/mutants.bash"

gate_slots=${GANDR_GATE_SLOTS:-2}

# Takes a free slot, waiting for one unless `GATE_NO_WAIT=1`, and records the
# holder as `$*`; sets `gate_slot` to its number.
hold_gate_slot() {
  local dir n holders announced=false
  [[ $gate_slots =~ ^[1-9][0-9]*$ ]] || { echo "check: GANDR_GATE_SLOTS is \`$gate_slots\`, not a count of slots" >&2; exit 2; }
  dir=$(mutants_lock_dir)
  dir=${dir%/}/gandr
  mkdir -p "$dir"
  while :; do
    for (( n = 1; n <= gate_slots; n++ )); do
      exec 9<> "$dir/gate.$n.lock"
      if mutants_flock 1; then
        printf '%s (pid %s, in %s, since %s)\n' "$*" "$$" "$PWD" "$(date -u +%FT%TZ)" > "$dir/gate.$n.lock"
        gate_slot=$n
        return 0
      fi
      exec 9<&-
    done
    holders=$(for (( n = 1; n <= gate_slots; n++ )); do printf '%s; ' "$(< "$dir/gate.$n.lock")"; done)
    holders=${holders%; }
    if [[ ${GATE_NO_WAIT:-} == 1 ]]; then
      echo "check: every gate slot on the host is held: $holders" >&2
      exit 2
    fi
    if [[ $announced == false ]]; then
      echo "check: waiting on $holders" >&2
      announced=true
    fi
    sleep 5
  done
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
