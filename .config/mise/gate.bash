# The gate graph's host-wide slot (#3057), sourced by `check`, `gate:all` and
# `.config/mise/gated`. Three seats' gates on one host pushed its load past 50
# on 32 cores, and the enforcing suite's slowest tests, which pass alone in 9 to
# 11 seconds, timed out at 30: a false red that costs a rerun and hides a real
# one. So a gate holds one of the host's gate slots for its whole run. The
# count is `GANDR_GATE_SLOTS` when it is set, and otherwise one slot for each
# 8 cores, at least one (#6699). `gate:all` runs one full test suite,
# `check:tests-enforcing`, as CI does (#5216), so the suite takes the host's
# cores divided by the slots, never more. The plain build runs only
# `check:tests-plain-only`, one test. The landing's gate, `check`, runs the
# enforcing suite of the packages its change touches alone (#6595), not of
# their dependents (#5458).
#
# One lane once held both slots, its two worktrees' gates running at once, and
# the host's load reached 70 on 32 cores (#4911). So a gate first takes its
# lane's one lock, `gate-lane-<lane>`, and only then a slot: a lane's second
# gate waits for its first, while another lane's gate takes the free slot. The
# lane is the longest lane of the factory's lane table
# (`.config/claims/lanes.bash`) that the worktree's name equals or starts with
# before a `-`, a leading `<repository>.` and a leading `lane-` dropped:
# `lane-flex-a`, `gandr.lane-flex-a` and `flex-a-6699-gate-slots` are all the
# lane `flex-a`, and `lane-flex-b` is another lane (#6699, #7046). A name that
# no lane of the table gives, or a host with no table, gives the name up to
# its first `-`: `surface-4911-gate-scope` is the lane `surface`. A heavy
# `check:*` task run alone (`check:doc`, `check:clippy*`, `check:dylint`,
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
#
# A background gate (#6638) takes its lane's lock and no slot. The head
# watcher of `landing` runs its gate with `GANDR_GATE_BACKGROUND=1` at
# niceness 19, so the gate takes only CPU that no other process asks for, and
# no lane's gate waits for its slot. A gate that asks for the background at
# another niceness takes a slot, as any gate does.
#
# Each run of `check` and `gate:all` leaves one row (#7021): one JSON line in
# `gates.jsonl` under `gandr/` in the host's state directory, which no tree
# holds. The row keeps the gate's times, its head, its tree, its lane, its
# slot, its waits, its result, the gates beside it and the host. One trap,
# `gate_exit`, writes the row and then releases the locks, whatever ends the
# gate. `report:gates` reads the rows of the host and prints the medians.

source "${BASH_SOURCE[0]%/*}/host-lock.bash"
source "${BASH_SOURCE[0]%/*}/../claims/lanes.bash"

# One slot for each 8 cores (#6699). Nine rounds of four gates of a code
# edit on 32 cores select 4 slots. At 8 slots a gate runs past 15 minutes,
# and 4 and 6 slots differ by less than the noise. At 4 slots each gate
# takes 8 build jobs, and the cores stay full. No gate waits for a slot at
# 4, 6 or 8 slots: the time of a gate is its work (#6963).
gate_cores=$(getconf _NPROCESSORS_ONLN)
gate_slots=${GANDR_GATE_SLOTS:-$(( gate_cores / 8 > 1 ? gate_cores / 8 : 1 ))}
# The rows of the gates on this host (#7021).
gate_rows=${XDG_STATE_HOME:-$HOME/.local/state}/gandr/gates.jsonl

# The lane of the worktree the gate runs in: the longest lane of the lane
# table that the worktree's name equals or starts with before a `-`, else the
# name up to its first `-`. The name drops a leading `<repository>.` and then
# a leading `lane-`. A worktree that `wt` makes is `<repository>.<branch>`, and
# the repository is the directory that holds the common git directory: with
# that name kept, every lane's worktree `gandr.flex-…` read as the one lane
# `gandr.flex` (#7046). Outside a worktree, the working directory's name
# stands for it.
gate_lane() {
  local top name lane best= common
  top=$(git rev-parse --show-toplevel 2> /dev/null) || top=$PWD
  name=${top##*/}
  if common=$(git rev-parse --path-format=absolute --git-common-dir 2> /dev/null); then
    common=${common%/.git}
    name=${name#"${common##*/}".}
  fi
  name=${name#lane-}
  while IFS= read -r lane; do
    if [[ $name == "$lane" || $name == "$lane"-* ]] && (( ${#lane} > ${#best} )); then best=$lane; fi
  done < <(lanes_list)
  printf '%s\n' "${best:-${name%%-*}}"
}

# The niceness of the gate's shell, which a background gate reads (#6638).
# Under `SCHED_IDLE`, the policy of the head watcher's service, `ps` prints
# `-` in place of the niceness (#6656), and `nice` prints the niceness that
# the kernel keeps. A `nice` that takes no bare call, as on macOS, gives
# `ps` the reading.
gate_niceness() {
  nice 2> /dev/null || ps -o ni= -p $$ | tr -d ' '
}

# Sets `gate_clock` to the time now in microseconds, from `EPOCHREALTIME`
# with its point taken out (#7051). A bash older than 5 has no
# `EPOCHREALTIME`, and the time is then `SECONDS` in microseconds.
gate_clock() {
  if [[ -n ${EPOCHREALTIME:-} ]]; then
    gate_clock=${EPOCHREALTIME/[.,]/}
  else
    gate_clock=$(( SECONDS * 1000000 ))
  fi
}

# Sets `gate_seconds` to the whole seconds from the time `$1` to the time
# `$2`, both in microseconds, rounded down (#7051).
gate_seconds() {
  gate_seconds=$(( ($2 - $1) / 1000000 ))
}

# Takes the lane's lock and then a free slot, waiting for each unless
# `GATE_NO_WAIT=1`, and records the holder as `$*`; sets `gate_slot` to the
# slot's number and `gate_lane` to the lane, exports `GANDR_GATE_SLOT`, and
# releases both from the caller's `EXIT` trap. It sets `gate_wait_lane` and
# `gate_wait_slot` to the seconds that it waited for each (#6699): the gate
# prints them when it holds its slot, and its record keeps them
# (`gate_wait`). A background gate waits for no slot. Each wait is read in
# microseconds and rounded down to seconds (#7051), so a take of a few
# milliseconds reads 0 on either side of a second's edge.
hold_gate_slot() {
  local wait=() start
  gate_clock
  start=$gate_clock
  [[ $gate_slots =~ ^[1-9][0-9]*$ ]] || { echo "check: GANDR_GATE_SLOTS is \`$gate_slots\`, not a count of slots" >&2; exit 2; }
  if [[ ${GATE_NO_WAIT:-} == 1 ]]; then wait=(--no-wait); fi
  gate_lane=$(gate_lane)
  host_lock ${wait[@]+"${wait[@]}"} --fd 8 "gate-lane-$gate_lane" 1 "$@"
  gate_clock
  gate_seconds "$start" "$gate_clock"
  gate_wait_lane=$gate_seconds
  gate_wait_slot=0
  if [[ ${GANDR_GATE_BACKGROUND:-} == 1 && $(gate_niceness) == 19 ]]; then
    # The gate's checks are no background gates (#6656): a check that takes
    # a slot of its own, or a case that asks for one, reads no request here.
    unset GANDR_GATE_BACKGROUND
    gate_slot=background
    export GANDR_GATE_SLOT=$gate_slot
    # The trap releases descriptor 9 too; it holds no lock here.
    exec 9> /dev/null
  else
    unset GANDR_GATE_BACKGROUND
    gate_clock
    start=$gate_clock
    host_lock ${wait[@]+"${wait[@]}"} gate "$gate_slots" "$@" "(lane $gate_lane)"
    gate_clock
    gate_seconds "$start" "$gate_clock"
    gate_wait_slot=$gate_seconds
    gate_slot=$host_slot
    export GANDR_GATE_SLOT=$gate_slot
  fi
  gate_locked=1
  gate_clock
  gate_held=$gate_clock
  gate_beside
  trap gate_exit EXIT
}

# The gate's waits as its record keeps them: `{"lane": <s>, "slot": <s>}`. A
# gate that took no lock waited for none, so both read 0.
gate_wait() {
  printf '{"lane": %d, "slot": %d}\n' "${gate_wait_lane:-0}" "${gate_wait_slot:-0}"
}

# Opens the row of the gate `$1`, `check` or `gate:all` (#7021): reads its
# start and the gates beside it, and sets the trap that ends it, `gate_exit`.
# A heavy check run alone opens no row, since it is no gate. The task sets
# `gate_tree` to the tree of the work once it reads it.
gate_open() {
  gate_name=$1
  gate_clock
  gate_start=$gate_clock
  gate_beside
  trap gate_exit EXIT
}

# Raises `gate_beside_most` to the count of the other gates on the host now:
# the lane locks whose recorded holder is alive and is not this shell. Each
# gate holds its lane's lock for its whole run, a background gate too, and so
# does a heavy check run alone. A lane's lock that its holder released keeps
# the record of a holder that has exited. The read forks no process.
gate_beside() {
  local dir file record pid count=0
  dir=$(host_lock_dir)
  for file in "${dir%/}"/gandr/gate-lane-*.1.lock; do
    [[ -f $file ]] || continue
    IFS= read -r record < "$file" || [[ -n $record ]] || continue
    [[ $record =~ \(pid\ ([0-9]+), ]] || continue
    pid=${BASH_REMATCH[1]}
    if [[ $pid != "$$" ]] && kill -0 "$pid" 2> /dev/null; then count=$(( count + 1 )); fi
  done
  if (( count > ${gate_beside_most:-0} )); then gate_beside_most=$count; fi
}

# Sets the variable `$1` to a JSON string of `$2`, or to `null` when `$2` is
# empty or holds a character outside `[A-Za-z0-9._:/-]`, which no field of a
# row needs. So the row needs no escape, and the shell writes it with no
# `jq` and no subshell.
gate_json_text() {
  if [[ -n $2 && $2 =~ ^[A-Za-z0-9._:/-]+$ ]]; then printf -v "$1" '"%s"' "$2"; else printf -v "$1" 'null'; fi
}

# Appends the row of the gate that ends with status `$1` to `gate_rows`
# (#7021). A status of 0 from a gate that did not reach its end, which sets
# `gate_ran`, is a signal: bash runs the `EXIT` trap of a `SIGTERM`, a
# `SIGINT` or a `SIGHUP` with the status of the last command. So the row
# reads `stopped`, as it does for a status above 128, and its status is
# null. The host's class is the `class` of `host.json` under
# `$XDG_CONFIG_HOME/gandr`, `{"class": "<name>"}`, and its architecture is
# bash's `HOSTTYPE`. The shell builds the row, and `git rev-parse` is its one
# process; a gate of light checks also reads its lane, which no lock read.
# The row is one `printf` of less than 4,096 bytes to a file opened for
# append, so the rows of two gates never mix. A failed write prints one line
# and fails no gate.
gate_row() {
  local status=$1 result config text= class= head lane millis row
  local name_json head_json tree_json lane_json slot_json arch_json class_json
  if [[ $status == 0 && -z ${gate_ran:-} ]] || (( status > 128 )); then
    result=stopped
    status=null
  elif [[ $status == 0 ]]; then
    result=passed
  else
    result=failed
  fi
  config=${XDG_CONFIG_HOME:-$HOME/.config}/gandr/host.json
  if [[ -f $config ]]; then
    IFS= read -r -d '' text < "$config" || :
    if [[ $text =~ \"class\"[[:space:]]*:[[:space:]]*\"([^\"]*)\" ]]; then class=${BASH_REMATCH[1]}; fi
  fi
  head=$(git rev-parse --verify --quiet HEAD 2> /dev/null) || head=
  lane=${gate_lane:-}
  if [[ -z $lane ]]; then lane=$(gate_lane); fi
  gate_json_text name_json "$gate_name"
  gate_json_text head_json "$head"
  gate_json_text tree_json "${gate_tree:-}"
  gate_json_text lane_json "$lane"
  if [[ ${gate_slot:-} =~ ^[0-9]+$ ]]; then slot_json=$gate_slot; else gate_json_text slot_json "${gate_slot:-}"; fi
  gate_json_text arch_json "${HOSTTYPE:-}"
  gate_json_text class_json "$class"
  gate_clock
  millis=$(( (gate_clock - gate_start) / 1000 ))
  printf -v row '{"gate":%s,"start":%d,"held":%s,"end":%d,"seconds":%d.%03d,"head":%s,"tree":%s,"lane":%s,"slot":%s,"wait":{"lane":%d,"slot":%d},"status":%s,"result":"%s","beside":%d,"host":{"arch":%s,"cores":%d,"class":%s}}' \
    "$name_json" "$gate_start" "${gate_held:-null}" "$gate_clock" $(( millis / 1000 )) $(( millis % 1000 )) \
    "$head_json" "$tree_json" "$lane_json" "$slot_json" "${gate_wait_lane:-0}" "${gate_wait_slot:-0}" \
    "$status" "$result" "${gate_beside_most:-0}" "$arch_json" "$gate_cores" "$class_json"
  if ! { { [[ -d ${gate_rows%/*} ]] || mkdir -p "${gate_rows%/*}"; } && printf '%s\n' "$row" >> "$gate_rows"; } 2> /dev/null; then
    echo "$gate_name: the row of the gate is not written to $gate_rows" >&2
  fi
}

# The one trap that ends a gate (#7021): the row of an open gate, read before
# the release so that its count of the gates beside still holds, then the
# release of the lane's lock and the slot, and of the jobserver's FIFO. Each
# step guards its own failure, so the trap keeps the status of the gate.
gate_exit() {
  local status=$?
  if [[ -n ${gate_name:-} ]]; then
    gate_beside
    gate_row "$status"
  fi
  if [[ -n ${gate_locked:-} ]]; then
    host_unlock 9 || :
    host_unlock 8 || :
  fi
  if [[ -n ${gate_jobs_fifo:-} ]]; then rm -f "$gate_jobs_fifo" || :; fi
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
#
# A driver that a test starts takes the host's width unless `GANDR_JOBS` caps
# it, so the gate sets `GANDR_JOBS` to the share too, and keeps a lower one
# (#7447).
gate_bound() {
  local share
  share=$(( gate_cores / gate_slots ))
  (( share >= 1 )) || share=1
  NEXTEST_TEST_THREADS=$(gate_lower "${NEXTEST_TEST_THREADS:-}" "$share")
  GANDR_JOBS=$(gate_lower "${GANDR_JOBS:-}" "$share")
  export NEXTEST_TEST_THREADS GANDR_JOBS
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
  trap gate_exit EXIT
}

# The lower of a value already set, when it is a positive count, and a share.
gate_lower() {
  if [[ $1 =~ ^[1-9][0-9]*$ ]] && (( $1 < $2 )); then
    printf '%s\n' "$1"
  else
    printf '%s\n' "$2"
  fi
}
