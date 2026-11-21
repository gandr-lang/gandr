#!/usr/bin/env bash
# Refuses each Rust source of the tree, outside the reader of a Rust crate,
# that opts into rustc's own libraries: `rustc_private` or an
# `extern crate rustc_…`. The reader is the one crate on those libraries, so
# no other crate needs the `rustc-dev` component.
#
#   linked.bash [root]   the tree at `root`, the current directory by default
set -euo pipefail

root=${1:-.}
mapfile -t found < <(git -C "$root" grep -l -E '(feature\(rustc_private\)|extern crate rustc_)' -- '*.rs' ':!crates/runtime-rust-reader/' || true)
if ((${#found[@]} > 0)); then
  echo "check:rust-record: only crates/runtime-rust-reader links a library of rustc; these sources opt into rustc_private:" >&2
  printf '  %s\n' "${found[@]}" >&2
  exit 1
fi
echo "rust-record linked OK: no crate but the reader links a library of rustc"
