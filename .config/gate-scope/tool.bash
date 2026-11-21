#!/usr/bin/env bash
# Runs a binary of a workflow crate. A host builds the binary one time for
# each state of its source.
#
# A script that calls `cargo run` pays the start of Cargo at each call, and a
# new worktree pays a build. So a host keeps each binary under its cache
# directory.
#
# The paths of the commit name a kept binary by their objects. They are the
# directory of the crate and of each crate of the workspace that it depends
# on. The manifest of the workspace, the lock file and the pin of the
# toolchain are paths of the key too. A worktree whose commit holds those
# objects runs the kept binary and starts no Cargo.
#
# A worktree that changes one of those paths has no object to name. So it
# builds the binary through `cargo build` and runs it.
# - see: #8273
#
# usage: tool.bash <package> <binary> [argument]...
#
# The binary reads the target and the flags of its caller, since the key of
# a verdict binds them. The build of the binary reads none of them. A cross
# target builds a binary that the host cannot run. Other flags build each
# crate again. So the build runs with no such variable, and the binary runs
# with the caller's environment.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
root=${here%/.config/gate-scope}
package=${1:?usage: tool.bash <package> <binary> [argument]...}
binary=${2:?usage: tool.bash <package> <binary> [argument]...}
shift 2
directory=crates/${package#gandr-}
# The crates of the workspace that each package depends on. A hosted job
# names the same paths in the key of its cache of the binary.
# - see: `.github/workflows/landing-checks.yml`
case $package in
  gandr-workflow-gate) depends=(crates/workflow-github) ;;
  *) depends=() ;;
esac
paths=("$directory" "${depends[@]}" Cargo.toml Cargo.lock rust-toolchain.toml)
clean=(env -u CARGO_BUILD_TARGET -u RUSTFLAGS -u CARGO_ENCODED_RUSTFLAGS -u CARGO_BUILD_RUSTFLAGS)
if [[ -z $(git -C "$root" status --porcelain --untracked-files=all -- "${paths[@]}") ]]; then
  mapfile -t objects < <(git -C "$root" rev-parse "${paths[@]/#/HEAD:}")
  printf -v name '%.16s' "${objects[@]}"
  kept=${XDG_CACHE_HOME:-$HOME/.cache}/gandr/tools/$binary/$name
  if [[ ! -x $kept/bin/$binary ]]; then
    (cd "$root" && .config/mise/scope "${clean[@]}" cargo install --quiet --locked --debug --force --path "$directory" --bin "$binary" --root "$kept") >&2
    # The host keeps the six newest builds of a binary.
    mapfile -t builds < <(ls -1dt "${kept%/*}"/*/)
    for build in "${builds[@]:6}"; do rm -rf "$build"; done
  fi
  exec "$kept/bin/$binary" "$@"
fi
(cd "$root" && "${clean[@]}" cargo build --quiet --locked --package "$package" --bin "$binary") >&2
exec "${CARGO_TARGET_DIR:-$root/target}/debug/$binary" "$@"
