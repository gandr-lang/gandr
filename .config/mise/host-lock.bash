# The host-wide locks the workflow takes (#3105), sourced by `gate.bash`,
# `mutants.bash` and `ci:act`: the gate's slots (#3057), the mutation run's
# one lock (#2726) and `ci:act`'s two slots.
#
# `host_lock [--no-wait] <name> <slots> <holder>...` takes one of `<slots>`
# slots, `<name>.<n>.lock` under `gandr/` in the user's runtime directory
# (`host_lock_dir`). The slot is locked exclusively with `flock(2)` on file
# descriptor 9, so the lock belongs to the caller and everything it started.
# A killed holder never leaves a slot held: the kernel drops the lock once the
# last process holding the descriptor exits. The file names its holder (the
# holder words, the pid, the worktree and the start).
#
# With every slot held, `host_lock` prints `<name>: waiting on <holders>` once
# and tries again every 5 seconds; with `--no-wait` it refuses at once with
# status 2, naming them. It sets `host_slot` to the slot's number. A process
# keeps one host lock at a time, since each takes descriptor 9.
#
# The lock is `flock(1)`'s where the host has it and perl's `flock` where it
# has not (macOS); either way it belongs to the open file the caller keeps.

# Takes a free slot of `<name>`, waiting for one unless `--no-wait`, and
# records the holder; sets `host_slot` to its number.
host_lock() {
  local wait=true name slots dir n holders announced=false
  if [[ ${1:-} == --no-wait ]]; then
    wait=false
    shift
  fi
  name=${1:?host_lock [--no-wait] <name> <slots> <holder>...}
  slots=${2:?host_lock [--no-wait] <name> <slots> <holder>...}
  shift 2
  [[ $slots =~ ^[1-9][0-9]*$ ]] || { echo "$name: \`$slots\` is not a count of slots" >&2; exit 2; }
  dir=$(host_lock_dir)
  dir=${dir%/}/gandr
  mkdir -p "$dir"
  while :; do
    for (( n = 1; n <= slots; n++ )); do
      exec 9<> "$dir/$name.$n.lock"
      if host_flock; then
        printf '%s (pid %s, in %s, since %s)\n' "$*" "$$" "$PWD" "$(date -u +%FT%TZ)" > "$dir/$name.$n.lock"
        host_slot=$n
        return 0
      fi
      exec 9<&-
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

# The user's runtime directory, one per user on the host whatever a run's
# environment: `XDG_RUNTIME_DIR`, else `/run/user/<uid>` where a service's
# environment lacks it, else macOS's per-user temporary directory, read with
# `getconf` so a run with `TMPDIR` unset reads the same, else `/tmp`.
host_lock_dir() {
  if [[ -n ${XDG_RUNTIME_DIR:-} ]]; then
    printf '%s\n' "$XDG_RUNTIME_DIR"
  elif [[ -d /run/user/$UID ]]; then
    printf '%s\n' "/run/user/$UID"
  elif ! getconf DARWIN_USER_TEMP_DIR 2> /dev/null; then
    printf '/tmp\n'
  fi
}

# Locks file descriptor 9 exclusively without waiting; fails when another
# process holds it.
host_flock() {
  if command -v flock > /dev/null; then
    flock --nonblock 9
  else
    perl -MFcntl=:flock -e 'open(my $fh, ">&=", 9) or die "fd 9: $!"; flock($fh, LOCK_EX | LOCK_NB) or exit 1'
  fi
}
