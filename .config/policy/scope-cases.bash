#!/usr/bin/env bash
# A scoped policy run lints each workspace package that it builds (#6946),
# run by `check:dylint` after its own run, through its own command
# (`policy`). The case builds a scratch workspace of two packages:
# `policy-case-consumer`, and `policy-case-base`, which the consumer depends
# on. It runs the policy over the consumer alone, as a lane's gate runs it
# over the packages that its change reaches. The run builds the base through
# the driver, and the denied lints apply to it. Under `--no-deps` the driver
# loads no library for the base, so the compiler refuses each denied lint as
# unknown.
set -euo pipefail
declare -F policy > /dev/null || { echo "policy case: run it from check:dylint, which exports \`policy\`" >&2; exit 2; }
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
failed=0

fail() {
  echo "policy case FAILED: $1"
  echo "  got: $2"
  failed=1
}

# A library package named `$2` at `$1`, its crate documented, that holds one
# documented constant `$3` and depends on the packages `$4...`.
package() {
  local dir=$1 name=$2 constant=$3
  shift 3
  mkdir -p "$scratch/$dir/src"
  {
    printf '[package]\nname = "%s"\nversion = "0.0.0"\nedition = "2024"\npublish = false\n\n[dependencies]\n' "$name"
    for dependency in "$@"; do printf '%s = { path = "../%s" }\n' "$dependency" "${dependency#policy-case-}"; done
  } > "$scratch/$dir/Cargo.toml"
  printf '//! A package of the policy case.\n\n/// A constant of the case.\npub const %s: u32 = 1;\n' "$constant" > "$scratch/$dir/src/lib.rs"
}

printf '[workspace]\nmembers = ["base", "consumer"]\nresolver = "3"\n' > "$scratch/Cargo.toml"
package base policy-case-base BASE
package consumer policy-case-consumer CONSUMER policy-case-base
cargo generate-lockfile --offline --quiet --manifest-path "$scratch/Cargo.toml"

# The records of the case's crates go to the scratch directory, never to the
# workspace's evidence. Cargo writes its output plain, so the case reads its
# lines as text: CI sets `CARGO_TERM_COLOR=always`, and a colour code then
# stands between `Checking` and the package's name.
status=0
out=$(DYLINT_TOML=$(printf '[quenchant-dylints]\nevidence_directory = "%s"\n' "$scratch/records") CARGO_TERM_COLOR=never \
  policy --manifest-path "$scratch/Cargo.toml" --package policy-case-consumer 2>&1) || status=$?
if [[ $status != 0 || $out == *"unknown lint"* || $out != *"Checking policy-case-base"* ]]; then
  fail "#6946: a policy run over a package lints the workspace package that it depends on, with no lint unknown" "exit $status: $out"
fi

(( failed == 0 )) || exit 1
echo "policy case OK: a scoped run lints the workspace package that its package depends on"
