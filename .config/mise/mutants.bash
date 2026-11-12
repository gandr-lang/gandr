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

# Lists one crate's mutants and reads its witness items. The caller holds the
# mutants lock. This starts no test or cargo build. It writes the mutant list,
# rustdoc items, and group input under `$2`.
mutants_listed() {
  local crate=$1 output=$2 package targets doc
  shift 2
  local -a docs
  package=$(cargo metadata --locked --no-deps --format-version 1 | jq -c --arg crate "$crate" '.packages[] | select(.name == $crate)')
  if [[ -z "$package" ]]; then
    printf 'no workspace crate named %s\n' "$crate" >&2
    return 2
  fi
  mapfile -t docs < <(jq -r '[.targets[] | select(.kind | index("lib")) | .name] as $libs
    | .targets[] | select((.kind | index("lib")) or ((.kind | index("bin")) and (.name | IN($libs[]) | not)))
    | .name | gsub("-"; "_") | "target/evidence/doc/\(.).json"' <<< "$package")
  targets=$(jq -c '[.targets[] | select(.kind | index("test")) | .name]' <<< "$package")
  for doc in "${docs[@]}"; do
    [[ -f "$doc" ]] || { printf 'no rustdoc JSON for %s at %s\n' "$crate" "$doc" >&2; return 2; }
  done
  mkdir -p "$output"
  "${mutants_scope[@]}" cargo mutants --list --json --package "$crate" "$@" > "$output/list.json"
  for doc in "${docs[@]}"; do jq -f .config/mutants/items.jq "$doc"; done | jq -s 'add // []' > "$output/items.json"
  jq -n --arg package "$crate" --argjson targets "$targets" --argjson lib "$(jq '[.targets[] | select(.kind | index("lib"))] | length > 0' <<< "$package")" \
    '{package: $package, targets: $targets, lib: $lib}' > "$output/group-input.json"
}

# Groups a listed crate's mutants. The caller can filter `list.json` before it
# calls this function. It writes the groups and the unwitnessed names.
mutants_grouped() {
  local output=$1
  jq -n --slurpfile mutants "$output/list.json" --slurpfile items "$output/items.json" \
    --slurpfile input "$output/group-input.json" \
    '{mutants: $mutants[0], items: $items[0], package: $input[0].package, targets: $input[0].targets}' \
    | jq -f .config/mutants/groups.jq > "$output/groups.json"
  jq -r '.[] | select(.filter == null) | .names[]' "$output/groups.json" | sort -u > "$output/unwitnessed.txt"
}

# The key of each witnessed mutant's outcome (#6878). It writes
# `$3/keyed.json`, one `{name, id, key, filter, tests, unit}` for each mutant
# that a witness reaches, `id` its place in `list.json` from 1. The key
# hashes each input of the outcome: the toolchain, the flags of the host
# triple, the workspace manifest, `Cargo.lock`, the cargo and nextest
# settings, the timeout `$2`, the files of the crate `$1` and of each
# workspace crate that it depends on (tracked, changed and untracked), and
# the mutant's name, replacement and witnesses. An edit outside those files
# changes no key.
mutants_keyed() {
  local crate=$1 timeout=$2 output=$3 flags base line
  local -a dirs settings
  mapfile -t dirs < <(cargo metadata --locked --format-version 1 | jq -r --arg crate "$crate" '
    .workspace_root as $root
    | (.packages | map({key: .id, value: (.manifest_path | rtrimstr("/Cargo.toml") | ltrimstr($root + "/"))}) | from_entries) as $dirs
    | [.workspace_members[]] as $members
    | (.resolve.nodes | map({key: .id, value: [.deps[].pkg | select(IN($members[]))]}) | from_entries) as $deps
    | [first(.packages[] | select(.name == $crate) | .id)]
    | until(([.[], (.[] | $deps[.][])] | unique) == .; [.[], (.[] | $deps[.][])] | unique)
    | .[] | $dirs[.]')
  for line in Cargo.toml Cargo.lock .cargo/config.toml .config/nextest.toml; do [[ ! -f $line ]] || settings+=("$line"); done
  flags=CARGO_TARGET_$(rustc -vV | sed -n 's/^host: //p' | tr '[:lower:]-' '[:upper:]_')_RUSTFLAGS
  base=$({
    rustc -vV
    printf '%s\n%s\n' "${!flags:-}" "$timeout"
    git hash-object "${settings[@]}"
    git ls-files --stage -- "${dirs[@]}"
    git diff --binary HEAD -- "${dirs[@]}"
    git ls-files -z --others --exclude-standard -- "${dirs[@]}" | xargs -0 -r git hash-object
  } | git hash-object --stdin)
  jq -c --slurpfile list "$output/list.json" '
    ($list[0] | to_entries | map({key: .value.name, value: {id: (.key + 1), replacement: .value.replacement}}) | from_entries) as $by
    | [.[] | select(.filter != null) | . as $group
        | .names[] | {name: ., id: $by[.].id, replacement: $by[.].replacement, filter: $group.filter, tests: $group.tests, unit: $group.unit}]' \
    "$output/groups.json" > "$output/keyed.json"
  jq -c '.[] | [.name, .replacement, .filter]' "$output/keyed.json" | while IFS= read -r line; do
    printf '%s\n%s\n' "$base" "$line" | git hash-object --stdin
  done | jq -R . | jq -s --slurpfile keyed "$output/keyed.json" '[$keyed[0], .] | transpose | map(.[0] + {key: .[1]} | del(.replacement))' > "$output/keyed.json.next"
  mv "$output/keyed.json.next" "$output/keyed.json"
}

# The survivors of one witnessed run (`mutants:witnessed`'s outcome directory
# `$1`) as a Markdown table collapsed under a summary counting them. It lists
# each missed mutant, then each timeout. Unwitnessed mutants are a static gap.
# A `|` in a name is written `\|`, so `replace && with ||` stays in one cell.
# Returns 1 and prints nothing when no survivor exists.
mutants_survivors() {
  local out=$1 name count noun=survivors
  [[ -s "$out/missed.txt" || -s "$out/timeout.txt" ]] || return 1
  count=$(cat "$out/missed.txt" "$out/timeout.txt" | wc -l | tr -d ' ')
  (( count != 1 )) || noun=survivor
  printf '\n<details><summary>%s %s — alive</summary>\n\n| mutant | verdict |\n| --- | --- |\n' "$count" "$noun"
  while IFS= read -r name; do
    printf '| `%s` | missed |\n' "${name//|/\\|}"
  done < "$out/missed.txt"
  while IFS= read -r name; do printf '| `%s` | timeout |\n' "${name//|/\\|}"; done < "$out/timeout.txt"
  printf '\n</details>\n'
}
