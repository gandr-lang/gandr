#!/usr/bin/env bash
# Runs a binary of a workflow crate. A host builds the binary one time for
# each state of its source.
#
# A script that calls `cargo run` pays the start of Cargo at each call, and a
# new worktree pays a build. So a host keeps each binary under its cache
# directory. Four paths of the commit name a kept binary by their objects.
# They are the crate's directory, the workspace's manifest, the lock file and
# the pin of the toolchain. A worktree whose commit holds those objects runs
# the kept binary and starts no Cargo.
#
# A worktree that changes one of those paths has no object to name. So it
# runs the binary through `cargo run`.
# - see: #8273
#
# usage: tool.bash <package> <binary> [argument]...
#
# economy: the name holds no other crate of the workspace, so the launcher
# serves a crate with no path dependency. ceiling: a crate with one names the
# directory of that dependency here, or it stays on `cargo run`.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
root=${here%/.config/gate-scope}
package=${1:?usage: tool.bash <package> <binary> [argument]...}
binary=${2:?usage: tool.bash <package> <binary> [argument]...}
shift 2
directory=crates/${package#gandr-}
paths=("$directory" Cargo.toml Cargo.lock rust-toolchain.toml)
if [[ -z $(git -C "$root" status --porcelain --untracked-files=all -- "${paths[@]}") ]]; then
  mapfile -t objects < <(git -C "$root" rev-parse "${paths[@]/#/HEAD:}")
  printf -v name '%.16s' "${objects[@]}"
  kept=${XDG_CACHE_HOME:-$HOME/.cache}/gandr/tools/$binary/$name
  if [[ ! -x $kept/bin/$binary ]]; then
    (cd "$root" && .config/mise/scope cargo install --quiet --locked --debug --force --path "$directory" --bin "$binary" --root "$kept") >&2
    # The host keeps the six newest builds of a binary.
    mapfile -t builds < <(ls -1dt "${kept%/*}"/*/)
    for build in "${builds[@]:6}"; do rm -rf "$build"; done
  fi
  exec "$kept/bin/$binary" "$@"
fi
exec cargo run --quiet --locked --manifest-path "$root/Cargo.toml" --package "$package" --bin "$binary" -- "$@"
