# The gate graph's host-wide slot (#3057), sourced by `check` and by
# `.config/mise/gated`. Three seats' gates on one host pushed its load past 50
# on 32 cores, and the enforcing suite's slowest tests, which pass alone in 9 to
# 11 seconds, timed out at 30: a false red that costs a rerun and hides a real
# one. So `mise run check` holds one of `GANDR_GATE_SLOTS` (default 2) slots for
# its whole run. Its two test suites, `check:tests` and `check:tests-enforcing`,
# run at once, so each takes the host's cores divided by the slots and by the
# two suites, never more.
#
# One lane once held both slots, its two worktrees' gates running at once, and
# the host's load reached 70 on 32 cores (#4911). So a gate first takes its
# lane's one lock, `gate-lane-<lane>`, and only then a slot: a lane's second
# gate waits for its first, while another lane's gate takes the free slot. The
# lane is the worktree's name up to its first `-`, a leading `lane-` dropped:
# `lane-surface` and `surface-4911-gate-scope` are both the lane `surface`. A
# heavy `check:*` task run alone (`check:doc`, `check:clippy*`, `check:dylint`,
# `check:tests*`) takes its lane's lock and a slot as the gate does, through
# `.config/mise/gated`; inside a gate, which exports `GANDR_GATE_SLOT`, it
# takes none.
#
# A slot is the host lock `gate` (`host-lock.bash`, #3105): `gate.<n>.lock`
# under `gandr/` in the user's runtime directory, held with `flock(2)` for the
# gate and everything it started. The gate releases its lane's lock and its
# slot as it exits, so a daemon one of its steps started holds neither after it
# (#4421). With the lane's lock or every slot held, the gate prints
# `<lock>: waiting on <holders>` and tries again every 5 seconds; with
# `GATE_NO_WAIT=1`, which `check --no-wait` sets, it refuses at once, naming
# them.

source "${BASH_SOURCE[0]%/*}/host-lock.bash"

gate_slots=${GANDR_GATE_SLOTS:-2}

# The lane of the worktree the gate runs in: its directory's name up to the
# first `-`, a leading `lane-` dropped. Outside a worktree, the working
# directory's name stands for it.
gate_lane() {
  local top name
  top=$(git rev-parse --show-toplevel 2> /dev/null) || top=$PWD
  name=${top##*/}
  name=${name#lane-}
  printf '%s\n' "${name%%-*}"
}

# Takes the lane's lock and then a free slot, waiting for each unless
# `GATE_NO_WAIT=1`, and records the holder as `$*`; sets `gate_slot` to the
# slot's number and `gate_lane` to the lane, exports `GANDR_GATE_SLOT`, and
# releases both from the caller's `EXIT` trap.
hold_gate_slot() {
  local wait=()
  [[ $gate_slots =~ ^[1-9][0-9]*$ ]] || { echo "check: GANDR_GATE_SLOTS is \`$gate_slots\`, not a count of slots" >&2; exit 2; }
  if [[ ${GATE_NO_WAIT:-} == 1 ]]; then wait=(--no-wait); fi
  gate_lane=$(gate_lane)
  host_lock ${wait[@]+"${wait[@]}"} --fd 8 "gate-lane-$gate_lane" 1 "$@"
  host_lock ${wait[@]+"${wait[@]}"} gate "$gate_slots" "$@" "(lane $gate_lane)"
  gate_slot=$host_slot
  export GANDR_GATE_SLOT=$gate_slot
  trap 'host_unlock 9; host_unlock 8' EXIT
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
