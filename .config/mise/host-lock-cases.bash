#!/usr/bin/env bash
# The host lock's behaviour (#3105), pinned once for its three callers: in a
# scratch runtime directory, two holders take a lock's two slots and a third
# taker with `--no-wait` refuses, naming both; another lock name is
# unaffected; a holder killed outright frees its slot; a waiter takes the
# slot a holder leaves; and a slot stays held while a child of a killed
# holder still runs, as `act` does when `ci:act` is killed.
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
export XDG_RUNTIME_DIR=$scratch
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

(( failed == 0 )) || exit 1
echo "host-lock check OK: a third taker refused naming both holders; names apart; a killed holder's slot freed; a waiter took a left slot; a running child kept its killed holder's slot"
