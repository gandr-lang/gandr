#!/usr/bin/env bash
# The cases of `linked.bash`. A tree passes when the reader is its only
# source on the libraries of rustc. A tree with one more such source is
# refused, and the refusal names the path of that source.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
tree=$(mktemp -d)
trap 'rm -rf "$tree"' EXIT
fail() { echo "linked-cases: $1" >&2; exit 1; }

git -C "$tree" init -q
mkdir -p "$tree/crates/runtime-rust-reader/src" "$tree/crates/core-other/src"
printf '#![feature(rustc_private)]\nextern crate rustc_driver;\n' > "$tree/crates/runtime-rust-reader/src/main.rs"
printf 'pub fn plain() {}\n' > "$tree/crates/core-other/src/lib.rs"
git -C "$tree" add -A
"$here/linked.bash" "$tree" > /dev/null || fail "a tree whose only rustc_private source is the reader is refused"

printf 'extern crate rustc_middle;\n' > "$tree/crates/core-other/src/lib.rs"
git -C "$tree" add -A
if output=$("$here/linked.bash" "$tree" 2>&1); then fail "a second crate on rustc's libraries passes"; fi
grep -q 'crates/core-other/src/lib.rs' <<< "$output" || fail "the refusal names the source: $output"
echo "rust-record linked cases OK: the reader passes alone, and a second crate is refused by its path"
