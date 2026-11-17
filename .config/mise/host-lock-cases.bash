#!/usr/bin/env bash
# These cases pin the host lock's behaviour once for its three callers, in a
# scratch lock directory. Two holders take a lock's two slots. One more taker
# with `--no-wait` gets no slot. Its message names both holders. Another lock
# name stays free.
# - see: #3105 — the host lock
#
# A kill of a holder frees its slot. A waiter takes the slot that a holder
# leaves. A child of a dead holder keeps the slot while it runs in the
# holder's process group. `act` does so after a kill of `ci:act`. A daemon in
# a group of its own keeps no slot, as `op daemon` does.
#
# A gate releases its slot as it exits, whether it ends or `TERM` stops it. A
# daemon of one of its steps keeps the descriptor open and holds no slot.
# - see: #4421 — the slot of a gate after its exit
#
# A lane holds one slot. A heavy check that runs alone takes one too. The lane
# table names the lanes, so two lanes whose names share a first word hold two
# slots. A gate that waits for its lane's lock gives that wait to its record.
# - see: #4911 — one slot for each lane
# - see: #6699 — the lane table and the wait of a gate
#
# The lock directory comes before the runtime directory. So a harness keeps
# its locks apart and leaves the runtime directory as it stands.
# - see: #6182 — the lock directory
#
# A gate draws on the host's counter where the `gandr` on the path has a
# `tokens` that runs a command. There the gate names its own `cargo`. That
# `cargo` runs the next `cargo` on the path through `gandr tokens --`. Beside
# an older `gandr`, the gate makes its own FIFO of its share.
# - see: #7688 — the gate's cargo on the host's counter
set -euo pipefail
helper=$(cd "${BASH_SOURCE[0]%/*}" && pwd)/host-lock.bash
source "${BASH_SOURCE[0]%/*}/../cases/scratch.bash"
scratch=$(mktemp -d)
pids=()
cleanup() {
  local pid
  for pid in "${pids[@]}"; do kill -KILL "$pid" 2> /dev/null || true; done
  rm -rf "$scratch"
}
trap cleanup EXIT
export GANDR_HOST_LOCK_DIR=$scratch
# The cases read a lane table of their own, never the host's.
printf '[lane]\nflex-a = []\nflex-b = []\n' > "$scratch/lanes.toml"
export GANDR_LANES=$scratch/lanes.toml
# A gate that runs these cases in the background asks for no background
# gate here (#6656).
unset GANDR_GATE_SLOT GATE_NO_WAIT GANDR_GATE_BACKGROUND
failed=0
fail() {
  printf 'host-lock: %s\n' "$*" >&2
  failed=1
}

# Starts a holder of `probe` named `$1` that runs `$2` once it holds a slot;
# waits until it does.
hold() {
  local name=$1 then=$2
  bash -c 'source "$1"; host_lock --no-wait probe 2 "$2"; : > "$3/$2.held"; eval "$4"' _ "$helper" "$name" "$scratch" "$then" 2> /dev/null &
  pids+=("$!")
  holder=$!
  local tries=0
  until [[ -e $scratch/$name.held ]]; do
    (( ++tries < 100 )) || { fail "$name never took a slot"; return 1; }
    sleep 0.1
  done
}

# Tries `probe` once without waiting; prints its refusal and returns its status.
take() {
  bash -c 'source "$1"; host_lock --no-wait probe 2 taker' _ "$helper" 2>&1
}

hold a 'exec sleep 300'
a=$holder
hold b 'exec sleep 300'
b=$holder
status=0
refusal=$(take) || status=$?
[[ $status == 2 ]] || fail "a third taker of two held slots exited $status, not 2"
[[ $refusal == *"probe: every slot on the host is held: a (pid"*"; b (pid"* ]] || fail "the refusal names no holders: $refusal"
bash -c 'source "$1"; host_lock --no-wait other 1 other' _ "$helper" || fail "another lock's name was refused while probe's slots were held"

kill -KILL "$a"
wait "$a" 2> /dev/null || true
status=0
take > /dev/null || status=$?
[[ $status == 0 ]] || fail "a holder killed outright left its slot held"

rm -f "$scratch/b.held"
kill -KILL "$b"
wait "$b" 2> /dev/null || true
hold c 'exec sleep 300'
hold d 'exec sleep 300'
d=$holder
bash -c 'source "$1"; host_lock probe 2 waiter; : > "$2/waiter.held"' _ "$helper" "$scratch" 2> "$scratch/waiter.err" &
waiter=$!
pids+=("$waiter")
sleep 1
kill -KILL "$d"
wait "$d" 2> /dev/null || true
tries=0
until [[ -e $scratch/waiter.held ]]; do
  (( ++tries < 150 )) || { fail "a waiter never took the slot a holder left"; break; }
  sleep 0.1
done
[[ $(< "$scratch/waiter.err") == "probe: waiting on c (pid"*"; d (pid"* ]] || fail "the waiter named no holders: $(< "$scratch/waiter.err")"
wait "$waiter" 2> /dev/null || true

for pid in "${pids[@]}"; do kill -KILL "$pid" 2> /dev/null || true; done
for pid in "${pids[@]}"; do wait "$pid" 2> /dev/null || true; done
pids=()
hold e 'sleep 300 & echo $! > "$3/e.child.part"; mv "$3/e.child.part" "$3/e.child"; wait'
e=$holder
hold f 'exec sleep 300'
tries=0
until [[ -e $scratch/e.child ]]; do
  (( ++tries < 100 )) || { fail "e never started its child"; break; }
  sleep 0.1
done
child=$(< "$scratch/e.child")
pids+=("$child")
kill -KILL "$e"
wait "$e" 2> /dev/null || true
status=0
take > /dev/null || status=$?
[[ $status == 2 ]] || fail "a killed holder's running child left its slot free"
kill -KILL "$child"
sleep 0.2
status=0
take > /dev/null || status=$?
[[ $status == 0 ]] || fail "the slot stayed held after the holder's child exited"

# A holder starts a daemon that detaches into a process group of its own,
# keeping descriptor 9, and is killed outright, so no trap releases the slot.
# The next taker takes the slot at once, while the daemon still runs.
hold g 'perl -MPOSIX -e '\''exit if fork; POSIX::setsid(); open(my $f, ">", "$ARGV[0].part") or die; print $f $$; close $f; rename("$ARGV[0].part", $ARGV[0]); exec "sleep", "300"'\'' "$3/g.daemon"; exec sleep 300'
g=$holder
tries=0
until [[ -e $scratch/g.daemon ]]; do
  (( ++tries < 100 )) || { fail "g's daemon never started"; break; }
  sleep 0.1
done
daemon=$(< "$scratch/g.daemon")
pids+=("$daemon")
kill -KILL "$g"
wait "$g" 2> /dev/null || true
kill -0 "$daemon" 2> /dev/null || fail "g's daemon ended with its holder"
status=0
reclaim=$(take 2>&1) || status=$?
[[ $status == 0 ]] || fail "a killed holder's detached daemon kept its slot: $reclaim"
[[ $reclaim == *"its holder, pid $g, has exited"* ]] || fail "the reclaim named no holder: $reclaim"
kill -KILL "$daemon" 2> /dev/null || true

# A gate of one slot starts a detached daemon that keeps descriptor 9, then
# ends normally or is stopped by `TERM`; the next gate takes the slot at once.
gate_helper=${helper%/*}/gate.bash
for ending in ends TERM; do
  GANDR_GATE_SLOTS=1 bash -c '
    source "$1"
    hold_gate_slot "gate that $2"
    setsid sleep 300 < /dev/null > /dev/null 2>&1 &
    echo $! > "$3/daemon.$2"
    : > "$3/gate.$2.held"
    if [[ $2 == TERM ]]; then sleep 300 & echo $! > "$3/step.$2"; wait; fi
  ' _ "$gate_helper" "$ending" "$scratch" > /dev/null 2>&1 &
  gate=$!
  pids+=("$gate")
  tries=0
  until [[ -e $scratch/gate.$ending.held && -s $scratch/daemon.$ending ]]; do
    (( ++tries < 100 )) || break
    sleep 0.1
  done
  [[ -e $scratch/gate.$ending.held ]] || { fail "#4421: the gate that $ending never took its slot"; continue; }
  pids+=("$(< "$scratch/daemon.$ending")")
  [[ ! -s $scratch/step.$ending ]] || pids+=("$(< "$scratch/step.$ending")")
  [[ $ending == ends ]] || kill -TERM "$gate"
  wait "$gate" 2> /dev/null || true
  status=0
  refusal=$(GANDR_GATE_SLOTS=1 bash -c 'source "$1"; GATE_NO_WAIT=1 hold_gate_slot taker' _ "$gate_helper" 2>&1) || status=$?
  [[ $status == 0 ]] || fail "#4421: a daemon kept the slot of the gate that $ending: $refusal"
done

for pid in "${pids[@]}"; do kill -KILL "$pid" 2> /dev/null || true; done
for pid in "${pids[@]}"; do wait "$pid" 2> /dev/null || true; done
pids=()

# A gate draws on the host's counter where the `gandr` on the path runs a
# command through `tokens`. Beside an older `gandr`, it makes its own FIFO of
# its share. The case's first `gandr` answers `tokens --help` as a build whose
# `tokens` runs a command. It writes each command that `tokens` runs.
# - see: #7688 — the gate's cargo on the host's counter
mkdir -p "$scratch/bin-7688" "$scratch/old-7688" "$scratch/cargo-7688"
printf '%s\n' '#!/usr/bin/env bash' \
  'if [[ $1 == tokens && $2 == --help ]]; then echo "Usage: gandr tokens [OPTIONS] -- <COMMAND>..."; exit 0; fi' \
  'if [[ $1 == tokens && $2 == -- ]]; then shift 2; echo "tokens runs: $*"; exit 0; fi' \
  'exit 2' > "$scratch/bin-7688/gandr"
printf '%s\n' '#!/usr/bin/env bash' 'echo "Usage: gandr tokens [OPTIONS]"' > "$scratch/old-7688/gandr"
printf '%s\n' '#!/usr/bin/env bash' 'echo cargo' > "$scratch/cargo-7688/cargo"
chmod +x "$scratch/bin-7688/gandr" "$scratch/old-7688/gandr" "$scratch/cargo-7688/cargo"
gate_bin=$(cd "${gate_helper%/*}/gate-bin" && pwd)
for build in bin-7688 old-7688; do
  status=0
  bound=$(PATH="$scratch/$build:$PATH" bash -c '
    source "$1"
    unset MAKEFLAGS NEXTEST_TEST_THREADS GANDR_JOBS GANDR_GATE_BIN
    gate_cores=8
    gate_slots=4
    gate_bound
    printf "%s\n%s\n%s\n" "$MAKEFLAGS" "$gate_jobs" "${GANDR_GATE_BIN:-none}"
  ' _ "$gate_helper" 2>&1) || status=$?
  [[ $status == 0 ]] || fail "#7688: the gate's bound beside $build exited $status: $bound"
  case $build in
    bin-7688) [[ $bound == "-j2"$'\n'"the host's counter's"$'\n'"$gate_bin" ]] || fail "#7688: the gate does not draw on the counter of a build whose tokens runs a command: $bound" ;;
    old-7688) [[ $bound == "-j2 --jobserver-auth=fifo:"*/gandr-gate-jobs.*$'\n'2$'\n'none ]] || fail "#7688: the gate beside an older build makes no FIFO of its share of 2: $bound" ;;
  esac
done

# On the counter, the gate names the directory of its `cargo`. `MAKEFLAGS`
# keeps the share and names no jobserver. A `gandr` whose `tokens` runs no
# command leaves the gate's flags as they stand.
# - see: #7688 — the gate's cargo on the host's counter
for build in bin-7688 old-7688; do
  status=0
  hosted=$(PATH="$scratch/$build:$PATH" bash -c '
    source "$1"
    unset GANDR_GATE_BIN
    MAKEFLAGS=inherited
    gate_hosted 2 || echo refused
    printf "%s\n%s\n" "$MAKEFLAGS" "${GANDR_GATE_BIN:-none}"
  ' _ "$gate_helper" 2>&1) || status=$?
  [[ $status == 0 ]] || fail "#7688: gate_hosted beside $build exited $status: $hosted"
  case $build in
    bin-7688) [[ $hosted == "-j2"$'\n'"$gate_bin" ]] || fail "#7688: the gate on the counter names no directory of its shim: $hosted" ;;
    old-7688) [[ $hosted == refused$'\n'inherited$'\n'none ]] || fail "#7688: the gate draws on a build whose tokens runs no command: $hosted" ;;
  esac
done

# The gate's `cargo` runs the next `cargo` on the path, past its own
# directory, through `gandr tokens --`.
# - see: #7688 — the gate's cargo on the host's counter
status=0
ran=$(PATH="$gate_bin:$scratch/bin-7688:$scratch/cargo-7688:$PATH" GANDR_GATE_BIN=$gate_bin "$gate_bin/cargo" --locked -q 2>&1) || status=$?
[[ $status == 0 && $ran == "tokens runs: $scratch/cargo-7688/cargo --locked -q" ]] || fail "#7688: the gate's shim runs no next program of its name through gandr tokens: $ran"

# A lane holds one slot (#4911). Of two slots, a gate of the lane `surface`
# holds one. A second gate of that lane refuses with `--no-wait`, naming the
# lane's lock, and otherwise waits on it, while a gate of the lane `core` takes
# the free slot. The waiter takes its slot once the first gate ends. The
# worktrees' names give the lanes: `lane-surface` and `surface-4911-scope` are
# both `surface`.
gated=${helper%/*}/gated
mkdir -p "$scratch/lane-surface" "$scratch/surface-4911-scope" "$scratch/core-1"
gate_in() {
  local dir=$1
  shift
  (cd "$scratch/$dir" && GANDR_GATE_SLOTS=2 exec bash -c "$@")
}
gate_in lane-surface 'source "$1"; hold_gate_slot first; echo $$ > "$2/first.pid"; : > "$2/first.held"; exec sleep 300' _ "$gate_helper" "$scratch" > /dev/null 2>&1 &
pids+=("$!")
tries=0
until [[ -e $scratch/first.held ]]; do
  (( ++tries < 100 )) || { fail "#4911: the lane's first gate never took its slot"; break; }
  sleep 0.1
done
first=$(< "$scratch/first.pid")
pids+=("$first")
status=0
refusal=$(gate_in surface-4911-scope 'source "$1"; GATE_NO_WAIT=1 hold_gate_slot second' _ "$gate_helper" 2>&1) || status=$?
[[ $status == 2 ]] || fail "#4911: a lane's second gate exited $status beside its first, not 2"
[[ $refusal == "gate-lane-surface: every slot on the host is held: first (pid"* ]] || fail "#4911: a lane's second gate named no lane lock: $refusal"
status=0
gate_in core-1 'source "$1"; GATE_NO_WAIT=1 hold_gate_slot other' _ "$gate_helper" > /dev/null 2>&1 || status=$?
[[ $status == 0 ]] || fail "#4911: another lane's gate found no free slot beside the first lane's gate"
gate_in surface-4911-scope 'echo $$ > "$2/lane-waiter.pid"; source "$1"; hold_gate_slot waiter; gate_wait > "$2/lane-waiter.wait"; : > "$2/lane-waiter.held"' _ "$gate_helper" "$scratch" 2> "$scratch/lane-waiter.err" &
waiter=$!
pids+=("$waiter")
sleep 1
[[ ! -s $scratch/lane-waiter.pid ]] || pids+=("$(< "$scratch/lane-waiter.pid")")
[[ ! -e $scratch/lane-waiter.held ]] || fail "#4911: a lane's second gate took a slot while its first gate ran"
kill -KILL "$first"
wait "$first" 2> /dev/null || true
tries=0
until [[ -e $scratch/lane-waiter.held ]]; do
  (( ++tries < 100 )) || { fail "#4911: the lane's waiting gate never took a slot after the first ended"; break; }
  sleep 0.1
done
[[ $(< "$scratch/lane-waiter.err") == "gate-lane-surface: waiting on first (pid"* ]] || fail "#4911: the lane's waiting gate named no lane lock: $(< "$scratch/lane-waiter.err")"
# The waiter's wait stands in its record (#6699): it waited for its lane's
# lock from before the first gate ended, and a slot was free once it held it.
jq -e '.lane >= 1 and .slot == 0' "$scratch/lane-waiter.wait" > /dev/null 2>&1 \
  || fail "#6699: the lane's waiting gate gave no wait for its lane's lock: $(< "$scratch/lane-waiter.wait")"
wait "$waiter" 2> /dev/null || true

# A wait reads whole seconds rounded down from microseconds (#7051): a take
# of 2 µs across a second's edge reads 0, and one whole second reads 1. So a
# slot taken at once reads no wait under a whole gate's load.
seconds=$(bash -c 'source "$1"; gate_seconds 999999 1000001; echo "$gate_seconds"; gate_seconds 0 1000000; echo "$gate_seconds"' _ "$gate_helper")
[[ $seconds == $'0\n1' ]] || fail "#7051: a wait across a second's edge read whole seconds of the clock, not of the wait: $seconds"
clock=$(bash -c 'source "$1"; gate_clock; a=$gate_clock; gate_clock; [[ $a =~ ^[0-9]+$ ]] && (( gate_clock >= a )) && echo ok' _ "$gate_helper")
[[ $clock == ok ]] || fail "#7051: the gate's clock gave no rising count of microseconds"

# The lane table names the lanes (#6699). The worktrees `lane-flex-a` and
# `lane-flex-b` are two lanes of the table, so their gates take two slots at
# once. The worktree of a branch, `flex-a-6699-scope`, is the lane `flex-a`,
# so its gate refuses beside the gate of `lane-flex-a`, naming that lane's
# lock.
mkdir -p "$scratch/lane-flex-a" "$scratch/lane-flex-b" "$scratch/flex-a-6699-scope"
gate_in lane-flex-a 'source "$1"; hold_gate_slot flex-a; echo $$ > "$2/flex-a.pid"; : > "$2/flex-a.held"; exec sleep 300' _ "$gate_helper" "$scratch" > /dev/null 2>&1 &
pids+=("$!")
tries=0
until [[ -e $scratch/flex-a.held ]]; do
  (( ++tries < 100 )) || { fail "#6699: the gate of the lane flex-a never took its slot"; break; }
  sleep 0.1
done
flex_a=$(< "$scratch/flex-a.pid")
pids+=("$flex_a")
status=0
refusal=$(gate_in lane-flex-b 'source "$1"; GATE_NO_WAIT=1 hold_gate_slot flex-b' _ "$gate_helper" 2>&1) || status=$?
[[ $status == 0 ]] || fail "#6699: the gate of the lane flex-b waited for the gate of the lane flex-a: exit $status, $refusal"
status=0
refusal=$(gate_in flex-a-6699-scope 'source "$1"; GATE_NO_WAIT=1 hold_gate_slot branch' _ "$gate_helper" 2>&1) || status=$?
[[ $status == 2 && $refusal == "gate-lane-flex-a: every slot on the host is held: flex-a (pid"* ]] \
  || fail "#6699: the gate of a branch of the lane flex-a took no lock of that lane: exit $status, $refusal"
kill -KILL "$flex_a"
wait "$flex_a" 2> /dev/null || true

# A worktree that `wt` makes is `<repository>.<branch>` (#7046). The
# repository's name and its `.` drop before the lane table is read, so the
# worktrees `repo.flex-a-7046-lane` and `repo.lane-flex-b` are the lanes
# `flex-a` and `flex-b`, not `repo.flex` and `repo.lane`.
git init --quiet "$scratch/repo"
identity "$scratch/repo"
git -C "$scratch/repo" commit --quiet --allow-empty -m root
for tree in flex-a-7046-lane lane-flex-b; do
  git -C "$scratch/repo" worktree add --quiet --detach "$scratch/repo.$tree"
done
lanes=$(for tree in flex-a-7046-lane lane-flex-b; do
  (cd "$scratch/repo.$tree" && bash -c 'source "$1"; gate_lane' _ "$gate_helper")
done | paste -sd ' ' -)
[[ $lanes == 'flex-a flex-b' ]] || fail "#7046: the worktrees repo.flex-a-7046-lane and repo.lane-flex-b gave the lanes $lanes"

# A heavy check run alone holds a slot through `gated`, so another lane's gate
# finds none of one slot free; inside a gate, which exports `GANDR_GATE_SLOT`,
# `gated` takes none.
(cd "$scratch/lane-surface" && GANDR_GATE_SLOTS=1 exec "$gated" bash -c 'echo $$ > "$1/alone.pid"; : > "$1/alone.held"; exec sleep 300' _ "$scratch") > /dev/null 2>&1 &
alone=$!
pids+=("$alone")
tries=0
until [[ -e $scratch/alone.held ]]; do
  (( ++tries < 100 )) || { fail "#4911: a heavy check run alone never ran"; break; }
  sleep 0.1
done
[[ ! -s $scratch/alone.pid ]] || pids+=("$(< "$scratch/alone.pid")")
status=0
refusal=$(cd "$scratch/core-1" && GANDR_GATE_SLOTS=1 GATE_NO_WAIT=1 bash -c 'source "$1"; hold_gate_slot taker' _ "$gate_helper" 2>&1) || status=$?
[[ $status == 2 && $refusal == "gate: every slot on the host is held: mise run "*" alone"* ]] || fail "#4911: a heavy check run alone held no slot: $refusal"
status=0
(cd "$scratch/core-1" && GANDR_GATE_SLOT=1 GANDR_GATE_SLOTS=1 GATE_NO_WAIT=1 "$gated" true) > /dev/null 2>&1 || status=$?
[[ $status == 0 ]] || fail "#4911: a heavy check inside a gate took a slot of its own"

# A background gate (#6638), at niceness 19, takes its lane's lock and no
# slot, so it runs while the one slot is held. Asked at niceness 0, it takes
# a slot as any gate does, and with the slot held it is refused. The case
# reads niceness 0 through `gate_niceness`, since a case that runs at
# niceness 19 cannot lower its own.
status=0
(cd "$scratch/core-1" && GANDR_GATE_BACKGROUND=1 GANDR_GATE_SLOTS=1 GATE_NO_WAIT=1 \
  nice -n 19 bash -c 'source "$1"; hold_gate_slot watcher; [[ $gate_slot == background ]]' _ "$gate_helper") > /dev/null 2>&1 || status=$?
[[ $status == 0 ]] || fail "#6638: a background gate at niceness 19 waited for a host slot, exit $status"
status=0
refusal=$(cd "$scratch/core-1" && GANDR_GATE_BACKGROUND=1 GANDR_GATE_SLOTS=1 GATE_NO_WAIT=1 \
  bash -c 'source "$1"; gate_niceness() { echo 0; }; hold_gate_slot watcher' _ "$gate_helper" 2>&1) || status=$?
[[ $status == 2 && $refusal == "gate: every slot on the host is held: mise run "*" alone"* ]] \
  || fail "#6638: a background gate at niceness 0 took no slot: exit $status, $refusal"

# A check inside a background gate is no background gate (#6656). The
# background gate keeps its request from its checks, so a check of another
# lane that asks for a slot, at the gate's niceness 19, is refused while the
# one slot is held.
mkdir -p "$scratch/views-6656"
status=0
refusal=$(cd "$scratch/core-1" && GANDR_GATE_BACKGROUND=1 GANDR_GATE_SLOTS=1 GATE_NO_WAIT=1 \
  nice -n 19 bash -c 'source "$1"; hold_gate_slot watcher; cd "$2" && bash -c "source \"\$1\"; hold_gate_slot check" _ "$1"' \
  _ "$gate_helper" "$scratch/views-6656" 2>&1) || status=$?
[[ $status == 2 && $refusal == "gate: every slot on the host is held: mise run "*" alone"* ]] \
  || fail "#6656: a check inside a background gate took no slot: exit $status, $refusal"

# A background gate under `SCHED_IDLE`, the head watcher's policy, reads its
# niceness 19 too (#6656): `ps` prints `-` there, so the gate reads `nice`.
# Only Linux has the policy, so the case runs where `chrt` is.
if command -v chrt > /dev/null; then
  status=0
  (cd "$scratch/core-1" && GANDR_GATE_BACKGROUND=1 GANDR_GATE_SLOTS=1 GATE_NO_WAIT=1 \
    nice -n 19 chrt --idle 0 bash -c 'source "$1"; hold_gate_slot watcher; [[ $gate_slot == background ]]' _ "$gate_helper") > /dev/null 2>&1 || status=$?
  [[ $status == 0 ]] || fail "#6656: a background gate under SCHED_IDLE at niceness 19 waited for a host slot, exit $status"
fi

# The lock directory (#6182): with both variables set, a lock takes its file
# under `GANDR_HOST_LOCK_DIR`, and the runtime directory holds no lock.
mkdir -p "$scratch/runtime"
GANDR_HOST_LOCK_DIR=$scratch/apart XDG_RUNTIME_DIR=$scratch/runtime bash -c 'source "$1"; host_lock --no-wait apart 1 apart' _ "$helper" 2> /dev/null \
  || fail "#6182: a lock under its own directory was refused"
[[ -e $scratch/apart/gandr/apart.1.lock ]] || fail "#6182: a lock took no file under GANDR_HOST_LOCK_DIR"
[[ -z $(ls -A "$scratch/runtime") ]] || fail "#6182: a lock wrote under XDG_RUNTIME_DIR while GANDR_HOST_LOCK_DIR was set"

# The lease of a scratch directory (#7615). Under one prefix, a directory
# whose `held` no process locks is dead, one whose `held` a live holder locks
# stays, and one with no `held` stays, since a call makes it now. A call
# removes the dead one, keeps the two others, and makes its own directory with
# its `held` locked. A holder that `KILL` ends runs no trap, so its directory
# stays until the next call removes it.
leases=$scratch/leases
mkdir -p "$leases/case.dead" "$leases/case.live" "$leases/case.making"
: > "$leases/case.dead/held"
: > "$leases/case.live/held"
bash -c 'source "$1"; exec 6<> "$2/held"; host_flock 6; : > "$2/locked"; exec sleep 60' _ "$helper" "$leases/case.live" &
pids+=("$!")
tries=0
until [[ -e $leases/case.live/locked ]] || (( ++tries > 100 )); do sleep 0.05; done
bash -c 'source "$1"; host_scratch "$2/case"; echo "$host_scratch_dir" > "$2/made"; : > "$2/ready"; exec sleep 60' _ "$helper" "$leases" &
pids+=("$!")
leaser=$!
tries=0
until [[ -e $leases/ready ]] || (( ++tries > 100 )); do sleep 0.05; done
made=$(< "$leases/made")
[[ ! -e $leases/case.dead ]] || fail "#7615: a call kept a directory whose held no process locks"
[[ -e $leases/case.live ]] || fail "#7615: a call removed a directory whose held a live holder locks"
[[ -e $leases/case.making ]] || fail "#7615: a call removed a directory with no held"
[[ -f $made/held && ! -e $made/holding ]] || fail "#7615: a call made no held for its own directory: $made"
bash -c 'source "$1"; host_scratch "$2/case"' _ "$helper" "$leases"
[[ -e $made ]] || fail "#7615: a second call removed the directory of a live first call"
kill -KILL "$leaser"
wait "$leaser" 2> /dev/null || true
bash -c 'source "$1"; host_scratch "$2/case"' _ "$helper" "$leases"
[[ ! -e $made ]] || fail "#7615: a call kept the directory of a holder that KILL ended"

(( failed == 0 )) || exit 1
echo "host-lock check OK: a third taker refused naming both holders; names apart; a killed holder's slot freed; a waiter took a left slot; a running child kept its killed holder's slot; a detached daemon kept no slot of a killed holder; a gate's daemon kept no slot after the gate ended or was stopped; a gate drew on the host's counter beside a build whose tokens runs a command, and made its own FIFO of its share beside an older build; a lane's second gate waited while another lane's gate took the free slot and gave its wait; two lanes of the lane table that share a first word held two slots; a worktree <repository>.<branch> read as its lane; a heavy check run alone held a slot; a lock took its file under its own directory, not the runtime directory; a scratch directory's lease kept a live run's directory and freed a killed run's"
