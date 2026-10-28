# A mutation run's guards on the host, sourced by the mutation tasks: one run
# at a time, and each run's cargo-mutants in a capped scope.
#
# A run builds several trees at once and holds tens of gigabytes while it
# does, so two runs side by side, each sized for the host alone, exhaust it
# (#2540). `hold_mutants_lock` takes the host lock `mutants`, one slot
# (`host-lock.bash`, #3105), for the task and everything it started, so a
# killed run never leaves it held. When another run holds it, a second run
# prints `mutants: waiting on <holder>` and waits; with `MUTANTS_NO_WAIT=1`,
# which a task's `--no-wait` sets and its nested runs inherit, it refuses at
# once, naming the holder.
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

source "${BASH_SOURCE[0]%/*}/host-lock.bash"

hold_mutants_lock() {
  if [[ ${MUTANTS_NO_WAIT:-} == 1 ]]; then
    host_lock --no-wait mutants 1 "$@"
  else
    host_lock mutants 1 "$@"
  fi
}

mutants_scope=("$(cd "${BASH_SOURCE[0]%/*}" && pwd)/scope" -p MemoryMax=16G -p MemorySwapMax=0 -p OOMPolicy=continue)

# The survivors of one witnessed run (`mutants:witnessed`'s outcome directory
# `$1`) as a Markdown table collapsed under a summary counting them: each
# missed mutant with its verdict, `missed` or `unwitnessed` (no witness names
# its function), then each one timed out. A `|` in a name is written `\|`,
# the escape a table cell reads (#3371), so `replace && with ||` stays one
# cell. Returns 1 and prints nothing when none survives.
mutants_survivors() {
  local out=$1 name verdict count noun=survivors
  [[ -s "$out/missed.txt" || -s "$out/timeout.txt" ]] || return 1
  count=$(cat "$out/missed.txt" "$out/timeout.txt" | wc -l | tr -d ' ')
  (( count != 1 )) || noun=survivor
  printf '\n<details><summary>%s %s — alive</summary>\n\n| mutant | verdict |\n| --- | --- |\n' "$count" "$noun"
  while IFS= read -r name; do
    verdict=missed
    ! grep -Fxq -- "$name" "$out/unwitnessed.txt" || verdict=unwitnessed
    printf '| `%s` | %s |\n' "${name//|/\\|}" "$verdict"
  done < "$out/missed.txt"
  while IFS= read -r name; do printf '| `%s` | timeout |\n' "${name//|/\\|}"; done < "$out/timeout.txt"
  printf '\n</details>\n'
}
