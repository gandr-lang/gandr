#!/usr/bin/env bash
# Cargo's freshness after a restamp, under this tree's Cargo configuration,
# run by `check:build-state` over the cases in `freshness.json`. Each case
# builds a scratch crate with this tree's configuration, so its unit is older
# than the next commit. The case's `change` gives that commit: `modify`
# changes the crate's source, and `none` changes nothing.
#
# The case then restamps a record of the commit, as CI restamps a newer
# state's record. So each source takes a date before the unit. The case's
# `output` is what Cargo then does with the unit: `fresh` or `rebuilt`.
# - see: #3206, #7775
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
root=$(cd "$here/../.." && pwd)
source "$here/sources.bash"
source "$here/../cases/scratch.bash"
cases=$here/freshness.json
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-freshness.XXXXXX")
trap 'rm -rf "$work"' EXIT
# A scratch crate outside the tree reads no toolchain file, so it takes the
# tree's. The case reads the configuration, so no variable overrides it.
RUSTUP_TOOLCHAIN=$(awk -F'"' '$1 ~ /^channel *= *$/ { print $2 }' "$root/rust-toolchain.toml")
export RUSTUP_TOOLCHAIN
unset CARGO_BUILD_FINGERPRINT CARGO_TARGET_DIR
failed=0

write() { if [[ $1 == */* ]]; then mkdir -p "${1%/*}"; fi; printf '%s\n' "$2" > "$1"; }

# What Cargo does with the scratch crate's unit: `fresh` or `rebuilt`.
built() {
  cargo --config "$root/.cargo/config.toml" check --quiet --message-format json |
    jq -r 'select(.reason == "compiler-artifact" and .target.name == "scratch") | if .fresh then "fresh" else "rebuilt" end'
}

count=$(jq length "$cases")
for (( i = 0; i < count; i++ )); do
  name=$(jq -r ".[$i].name" "$cases")
  change=$(jq -r ".[$i].change" "$cases")
  expected=$(jq -r ".[$i].output" "$cases")
  dir=$work/$i
  git init --quiet "$dir"
  cd "$dir"
  identity
  printf 'target/\nCargo.lock\n' > .git/info/exclude
  write Cargo.toml $'[package]\nname = "scratch"\nversion = "0.0.0"\nedition = "2024"\n\n[workspace]'
  write src/lib.rs 'pub fn first() {}'
  git add . && git commit --quiet --message base
  built > /dev/null
  if [[ $change == modify ]]; then
    write src/lib.rs $'pub fn first() {}\npub fn second() {}'
    git add src/lib.rs && git commit --quiet --message next
  fi
  sources_record target/debug
  # A clone's checkout dates every path now, and the restamp then dates each
  # path that the record holds before any build.
  find . -path ./.git -prune -o -path ./target -prune -o -mindepth 1 -exec touch -h {} +
  sources_restamp target/debug/"$SOURCES_RECORD"
  actual=$(built)
  if [[ $actual != "$expected" ]]; then
    printf 'build-state freshness case %s\n  expected: %s\n  actual:   %s\n' "$name" "$expected" "$actual" >&2
    failed=1
  fi
done
(( failed == 0 )) || exit 1
echo "build-state freshness OK: $count cases build a restamped unit again only where its source changes"
