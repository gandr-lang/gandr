# A mutation run's guards on the host, sourced by the mutation tasks: one run
# at a time, and each run's cargo-mutants in a capped scope.
#
# A run builds several trees at once and holds tens of gigabytes while it
# does, so two runs side by side, each sized for the host alone, exhaust it
# (#2540). `hold_mutants_lock` takes an exclusive lock on
# `gandr-mutants.lock` in the user's runtime directory (`mutants_lock_dir`)
# and keeps it on file descriptor 9 until the task and everything it started
# have exited, so a killed run never leaves it held. The file names the holder
# (the command, its pid, worktree and start). When another run holds it, a
# second run prints `mutants: waiting on <holder>` and waits; with
# `MUTANTS_NO_WAIT=1`, which a task's `--no-wait` sets and its nested runs
# inherit, it refuses at once, naming the holder. The lock is `flock(2)`'s,
# taken with `flock(1)` where the host has it and through perl's `flock`
# where it has not (macOS): either way it belongs to the open file the task
# keeps.
#
# A mutant can turn a bounded loop into an unbounded allocation: one test
# binary reached 53 GB of memory and 76 GB of swap in about a minute, and
# swapping the host to its limit made systemd-oomd end the service that
# started the run. `mutants_scope` is the scope wrapper (`scope`, beside this
# file, by absolute path so a task can call it from a copy of the workspace)
# with hard caps:
# - `MemoryMax=16G`: the kernel's OOM killer acts inside the scope at the cap
#   and chooses its largest process, the runaway test, which then fails, so
#   the mutant reads caught. A dispatcher group's build and tests peaked at
#   1.8 GB, and `mutants` building four at once held 3.4 GB.
# - `MemorySwapMax=0`: the scope never swaps, so it reaches the cap in
#   seconds rather than swapping the host first.
# - `OOMPolicy=continue`: systemd's default ends the whole unit on an OOM
#   kill inside it, which would end the run with its one mutant.
# cargo-mutants' own `--timeout` still ends a mutant that loops without
# allocating.

hold_mutants_lock() {
  local lock
  lock=$(mutants_lock_dir)
  lock=${lock%/}/gandr-mutants.lock
  exec 9<> "$lock"
  if ! mutants_flock 1; then
    if [[ ${MUTANTS_NO_WAIT:-} == 1 ]]; then
      printf 'mutants: another cargo-mutants run holds %s: %s\n' "$lock" "$(< "$lock")" >&2
      exit 2
    fi
    printf 'mutants: waiting on %s\n' "$(< "$lock")" >&2
    mutants_flock 0
  fi
  printf '%s (pid %s, in %s, since %s)\n' "$*" "$$" "$PWD" "$(date -u +%FT%TZ)" > "$lock"
}

# The user's runtime directory, one per user on the host whatever a run's
# environment: `XDG_RUNTIME_DIR`, else `/run/user/<uid>` where a service's
# environment lacks it, else macOS's per-user temporary directory, read with
# `getconf` so a run with `TMPDIR` unset reads the same, else `/tmp`.
mutants_lock_dir() {
  if [[ -n ${XDG_RUNTIME_DIR:-} ]]; then
    printf '%s\n' "$XDG_RUNTIME_DIR"
  elif [[ -d /run/user/$UID ]]; then
    printf '%s\n' "/run/user/$UID"
  elif ! getconf DARWIN_USER_TEMP_DIR 2> /dev/null; then
    printf '/tmp\n'
  fi
}

# Lock file descriptor 9 exclusively, without waiting when `$1` is 1.
mutants_flock() {
  if command -v flock > /dev/null; then
    if [[ $1 == 1 ]]; then flock --nonblock 9; else flock 9; fi
  else
    perl -MFcntl=:flock -e 'open(my $fh, ">&=", 9) or die "fd 9: $!"; flock($fh, LOCK_EX | ($ARGV[0] ? LOCK_NB : 0)) or exit 1' "$1"
  fi
}

mutants_scope=("$(cd "${BASH_SOURCE[0]%/*}" && pwd)/scope" -p MemoryMax=16G -p MemorySwapMax=0 -p OOMPolicy=continue)

# The survivors of one witnessed run (`mutants:witnessed`'s outcome directory
# `$1`) as a Markdown table collapsed under a summary counting them: each
# missed mutant with its verdict, `missed` or `unwitnessed` (no witness names
# its function), then each one timed out. Returns 1 and prints nothing when
# none survives.
mutants_survivors() {
  local out=$1 name verdict count noun=survivors
  [[ -s "$out/missed.txt" || -s "$out/timeout.txt" ]] || return 1
  count=$(cat "$out/missed.txt" "$out/timeout.txt" | wc -l | tr -d ' ')
  (( count != 1 )) || noun=survivor
  printf '\n<details><summary>%s %s — alive</summary>\n\n| mutant | verdict |\n| --- | --- |\n' "$count" "$noun"
  while IFS= read -r name; do
    verdict=missed
    ! grep -Fxq -- "$name" "$out/unwitnessed.txt" || verdict=unwitnessed
    printf '| `%s` | %s |\n' "$name" "$verdict"
  done < "$out/missed.txt"
  while IFS= read -r name; do printf '| `%s` | timeout |\n' "$name"; done < "$out/timeout.txt"
  printf '\n</details>\n'
}
