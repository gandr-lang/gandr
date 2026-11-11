# The gate graph's host-wide slot (#3057), sourced by `check`, `gate:all` and
# `.config/mise/gated`. Three seats' gates on one host pushed its load past 50
# on 32 cores, and the enforcing suite's slowest tests, which pass alone in 9 to
# 11 seconds, timed out at 30: a false red that costs a rerun and hides a real
# one. So a gate holds one of `GANDR_GATE_SLOTS` (default 2) slots for its
# whole run. `gate:all` runs one full test suite, `check:tests-enforcing`, as CI
# does (#5216), so the suite takes the host's cores divided by the slots, never
# more. The plain build runs only `check:tests-plain-only`, one test. The
# landing's gate, `check`, runs the enforcing suite of the packages its change
# touches alone (#6595), not of their dependents (#5458).
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

# A gate's share of the host: the host's cores divided by the slots, at least
# one (#5424). The share bounds the suite's test threads,
# `NEXTEST_TEST_THREADS`, and the gate's builds as one pool. A gate runs up to
# 8 mise tasks at once, and each cargo among them starts one `rustc` for each
# core. A bound on each cargo (`CARGO_BUILD_JOBS`) multiplies by the count of
# cargo commands, so it does not bound the gate.
#
# So the gate makes one jobserver: a FIFO that holds one token for each job of
# the share. `MAKEFLAGS` names it as GNU make names its own
# (`--jobserver-auth=fifo:<path>`). Each cargo of the gate takes its tokens
# from the FIFO and gives them to `rustc`. A cargo also keeps one token of its
# own, so a gate runs at most the share plus one `rustc` for each cargo. A
# jobserver that `MAKEFLAGS` already names stays, and so does a lower
# `NEXTEST_TEST_THREADS`.
gate_bound() {
  local cores share
  cores=$(getconf _NPROCESSORS_ONLN)
  share=$(( cores / gate_slots ))
  (( share >= 1 )) || share=1
  NEXTEST_TEST_THREADS=$(gate_lower "${NEXTEST_TEST_THREADS:-}" "$share")
  export NEXTEST_TEST_THREADS
  gate_jobs=$share
  if [[ ${MAKEFLAGS:-} == *--jobserver-auth=* ]]; then
    gate_jobs="the inherited jobserver's"
    return
  fi
  gate_jobs_fifo=$(mktemp -u "${TMPDIR:-/tmp}/gandr-gate-jobs.XXXXXX")
  mkfifo -m 600 "$gate_jobs_fifo"
  exec {gate_jobs_fd}<>"$gate_jobs_fifo"
  printf '%*s' "$share" '' >&"$gate_jobs_fd"
  export MAKEFLAGS="-j$share --jobserver-auth=fifo:$gate_jobs_fifo"
  trap 'host_unlock 9; host_unlock 8; rm -f "$gate_jobs_fifo"' EXIT
}

# The lower of a value already set, when it is a positive count, and a share.
gate_lower() {
  if [[ $1 =~ ^[1-9][0-9]*$ ]] && (( $1 < $2 )); then
    printf '%s\n' "$1"
  else
    printf '%s\n' "$2"
  fi
}
