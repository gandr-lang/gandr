# The host-wide locks the workflow takes (#3105), sourced by `gate.bash`,
# `mutants.bash` and `ci:act`: the gate's slots (#3057), the mutation run's
# one lock (#2726) and `ci:act`'s two slots.
#
# `host_lock [--no-wait] [--fd <n>] <name> <slots> <holder>...` takes one of
# `<slots>` slots, `<name>.<n>.lock` under `gandr/` in the user's runtime
# directory (`host_lock_dir`). The slot is locked exclusively with `flock(2)` on
# file descriptor 9, or the one `--fd` names, so the lock belongs to the caller
# and everything it started.
# A killed holder never leaves a slot held: the kernel drops the lock once the
# last process holding the descriptor exits. The file names its holder (the
# holder words, the pid, its process group, the worktree and the start).
#
# A daemon a holder's child starts inherits descriptor 9 and outlives the
# holder: `op daemon`, which a signing or `gh` call starts, kept every gate
# slot on a host held for hours (#4421). `host_unlock` releases the lock for
# every process that shares the descriptor, so a holder calls it as it exits,
# from its `EXIT` trap. A holder killed outright runs no trap, so a waiter
# reclaims its slot (`host_reclaim`) when the holder the record names has
# exited and every process still holding the file is in another process
# group: a daemon detaches into a group of its own, while a child still doing
# the holder's work, such as `act` under a killed `ci:act`, stays in the
# holder's group and keeps the slot. The waiter removes the file and locks a
# new one, which no daemon holds.
#
# With every slot held, `host_lock` prints `<name>: waiting on <holders>` once
# and tries again every 5 seconds; with `--no-wait` it refuses at once with
# status 2, naming them. It sets `host_slot` to the slot's number. A process
# keeps one host lock per descriptor: the gate holds its lane's lock on
# descriptor 8 beside its slot on 9 (#4911).
#
# The lock is `flock(1)`'s where the host has it and perl's `flock` where it
# has not (macOS); either way it belongs to the open file the caller keeps.

# Takes a free slot of `<name>`, waiting for one unless `--no-wait`, and
# records the holder; sets `host_slot` to its number.
host_lock() {
  local wait=true fd=9 name slots dir n holders announced=false
  while :; do
    case ${1:-} in
      --no-wait) wait=false; shift ;;
      --fd) fd=${2:?--fd takes a descriptor}; shift 2 ;;
      *) break ;;
    esac
  done
  name=${1:?host_lock [--no-wait] [--fd <n>] <name> <slots> <holder>...}
  slots=${2:?host_lock [--no-wait] [--fd <n>] <name> <slots> <holder>...}
  shift 2
  [[ $fd =~ ^[0-9]$ ]] || { echo "$name: \`$fd\` is not a descriptor from 0 to 9" >&2; exit 2; }
  [[ $slots =~ ^[1-9][0-9]*$ ]] || { echo "$name: \`$slots\` is not a count of slots" >&2; exit 2; }
  dir=$(host_lock_dir)
  dir=${dir%/}/gandr
  mkdir -p "$dir"
  while :; do
    for (( n = 1; n <= slots; n++ )); do
      eval "exec $fd<> \"\$dir/\$name.\$n.lock\""
      if host_flock "$fd"; then
        printf '%s (pid %s, group %s, in %s, since %s)\n' "$*" "$$" "$(host_group "$$")" "$PWD" "$(date -u +%FT%TZ)" > "$dir/$name.$n.lock"
        host_slot=$n
        return 0
      fi
      eval "exec $fd<&-"
      # A slot only detached processes hold, its holder gone, is taken again.
      if host_reclaim "$dir/$name.$n.lock"; then n=$(( n - 1 )); fi
    done
    holders=$(for (( n = 1; n <= slots; n++ )); do printf '%s; ' "$(< "$dir/$name.$n.lock")"; done)
    holders=${holders%; }
    if [[ $wait == false ]]; then
      echo "$name: every slot on the host is held: $holders" >&2
      exit 2
    fi
    if [[ $announced == false ]]; then
      echo "$name: waiting on $holders" >&2
      announced=true
    fi
    sleep 5
  done
}

# The directory of the host locks: `GANDR_HOST_LOCK_DIR`, which a harness sets
# to keep its locks apart without moving the user's runtime directory (#6182).
# Without it, the user's runtime directory, one per user on the host whatever
# a run's environment: `XDG_RUNTIME_DIR`, else `/run/user/<uid>` where a
# service's environment lacks it, else macOS's per-user temporary directory,
# read with `getconf` so a run with `TMPDIR` unset reads the same, else `/tmp`.
host_lock_dir() {
  if [[ -n ${GANDR_HOST_LOCK_DIR:-} ]]; then
    printf '%s\n' "$GANDR_HOST_LOCK_DIR"
  elif [[ -n ${XDG_RUNTIME_DIR:-} ]]; then
    printf '%s\n' "$XDG_RUNTIME_DIR"
  elif [[ -d /run/user/$UID ]]; then
    printf '%s\n' "/run/user/$UID"
  elif ! getconf DARWIN_USER_TEMP_DIR 2> /dev/null; then
    printf '/tmp\n'
  fi
}

# The process group of process `$1`.
host_group() {
  ps -o pgid= -p "$1" 2> /dev/null | tr -d ' '
}

# The holder pid and its process group that lock file `$1`'s record names,
# as `<pid> <group>`, or nothing.
host_holder() {
  sed -n 's/.*(pid \([0-9][0-9]*\), group \([0-9][0-9]*\), in .*/\1 \2/p' "$1" 2> /dev/null | sed -n 1p
}

# The pids that hold file `$1` open: `lsof` where the host has it, else
# `/proc`.
host_file_holders() {
  local fd
  if command -v lsof > /dev/null; then
    lsof -t -- "$1" 2> /dev/null || :
    return 0
  fi
  for fd in /proc/[0-9]*/fd/*; do
    if [[ $(readlink "$fd" 2> /dev/null) == "$1" ]]; then
      fd=${fd#/proc/}
      echo "${fd%%/*}"
    fi
  done
}

# Removes lock file `$1` and succeeds when the holder its record names has
# exited and every process that still holds the file is in another process
# group than that holder's; fails, leaving it, otherwise. The record is read
# again inside a guard directory, so a waiter never removes a file that
# another waiter has already replaced: a new file is empty until its holder
# writes its own record.
host_reclaim() {
  local file=$1 record pid group holder status=1
  record=$(host_holder "$file")
  [[ -n $record ]] || return 1
  pid=${record% *}
  group=${record#* }
  ! kill -0 "$pid" 2> /dev/null || return 1
  for holder in $(host_file_holders "$file"); do
    [[ $(host_group "$holder") != "$group" ]] || return 1
  done
  mkdir "$file.reclaim" 2> /dev/null || return 1
  if [[ $(host_holder "$file") == "$record" ]]; then
    rm -f -- "$file"
    echo "${file##*/}: its holder, pid $pid, has exited, and only processes outside its process group hold it; the slot is taken again" >&2
    status=0
  fi
  rmdir "$file.reclaim"
  return "$status"
}

# Releases the lock on file descriptor `$1` (default 9) for every process
# sharing it, a daemon that inherited it included.
host_unlock() {
  local fd=${1:-9}
  if command -v flock > /dev/null; then
    flock --unlock "$fd"
  else
    perl -MFcntl=:flock -e 'open(my $fh, ">&=", $ARGV[0]) or die "fd $ARGV[0]: $!"; flock($fh, LOCK_UN)' "$fd"
  fi
}

# Locks file descriptor `$1` exclusively without waiting; fails when another
# process holds it.
host_flock() {
  local fd=$1
  if command -v flock > /dev/null; then
    flock --nonblock "$fd"
  else
    perl -MFcntl=:flock -e 'open(my $fh, ">&=", $ARGV[0]) or die "fd $ARGV[0]: $!"; flock($fh, LOCK_EX | LOCK_NB) or exit 1' "$fd"
  fi
}
