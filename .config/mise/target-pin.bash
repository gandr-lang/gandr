#!/usr/bin/env bash
# The build directory remembers the compiler that filled it (#7497). Cargo
# writes that record itself: `.rustc_info.json` at the root of the target
# holds the output of `rustc -vV` for the compiler that last ran there. No
# second record stands beside it.
#
# Before the first build of a gate or of a new worktree, this step reads the
# record and compares its compiler with the tree's compiler, which
# `rust-toolchain.toml` pins. One compiler keeps the target. A difference runs
# `cargo clean`, since the units of the other compiler are dead weight on the
# disk. The first build under a new pin is cold anyway. A target with no
# record, or a record that names no compiler, has nothing to clean.
#
# It runs from the root of the tree, as each caller does, so the toolchain
# proxy reads the tree's pin. The target is `CARGO_TARGET_DIR`, or `target`.
# A `rustc` that does not run stops the caller by name, and so does a failed
# clean.
set -euo pipefail
target=${CARGO_TARGET_DIR:-target}
record=$target/.rustc_info.json
[[ -f $record ]] || exit 0
built=$(jq -r '[.outputs[]?.stdout | strings | split("\n")[] | select(startswith("commit-hash: ")) | ltrimstr("commit-hash: ")] | unique | join(" ")' "$record" 2> /dev/null) || built=
[[ -n $built ]] || exit 0
if ! current=$(rustc -vV 2>&1); then
  echo "target:pin: rustc -vV fails in $PWD, so no build runs: $current" >&2
  exit 1
fi
hash=$(sed -n 's/^commit-hash: //p' <<< "$current")
[[ $built != "$hash" ]] || exit 0
was=$(jq -r '[.outputs[]?.stdout | strings | split("\n")[0] | select(startswith("rustc "))] | unique | join(", ")' "$record")
echo "target:pin: $target holds the units of ${was:-the compiler $built}, and the tree pins ${current%%$'\n'*}, so cargo clean takes them out" >&2
if ! cargo clean; then
  echo "target:pin: cargo clean of $target fails, so no build runs" >&2
  exit 1
fi
