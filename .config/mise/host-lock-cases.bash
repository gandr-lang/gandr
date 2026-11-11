#!/usr/bin/env bash
# The host lock's behaviour (#3105), pinned once for its three callers: in a
# scratch lock directory, two holders take a lock's two slots and a third
# taker with `--no-wait` refuses, naming both; another lock name is
# unaffected; a holder killed outright frees its slot; a waiter takes the
# slot a holder leaves; and a slot stays held while a child of a killed
# holder still runs in its process group, as `act` does when `ci:act` is
# killed, but not while only a daemon in a group of its own holds it, as `op
# daemon` does. A gate releases its slot as it exits, whether it ends or is
# stopped by `TERM`, while a daemon one of its steps started keeps the
# descriptor open (#4421). A lane holds one slot, and a heavy check run alone
# takes one (#4911). The lock directory comes before the runtime directory,
# so a harness keeps its locks apart without moving the runtime directory
# (#6182).
set -euo pipefail
helper=$(cd "${BASH_SOURCE[0]%/*}" && pwd)/host-lock.bash
scratch=$(mktemp -d)
pids=()
cleanup() {
  local pid
  for pid in "${pids[@]}"; do kill -KILL "$pid" 2> /dev/null || true; done
  rm -rf "$scratch"
}
trap cleanup EXIT
export GANDR_HOST_LOCK_DIR=$scratch
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
gate_in surface-4911-scope 'echo $$ > "$2/lane-waiter.pid"; source "$1"; hold_gate_slot waiter; : > "$2/lane-waiter.held"' _ "$gate_helper" "$scratch" 2> "$scratch/lane-waiter.err" &
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
wait "$waiter" 2> /dev/null || true

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

(( failed == 0 )) || exit 1
echo "host-lock check OK: a third taker refused naming both holders; names apart; a killed holder's slot freed; a waiter took a left slot; a running child kept its killed holder's slot; a detached daemon kept no slot of a killed holder; a gate's daemon kept no slot after the gate ended or was stopped; a lane's second gate waited while another lane's gate took the free slot; a heavy check run alone held a slot; a lock took its file under its own directory, not the runtime directory"
