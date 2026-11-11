#!/usr/bin/env bash
# Prints the policy configuration that the record run of `check:deletes`
# gives `cargo dylint` at a tree: the `DYLINT_TOML` of that tree's own
# `check:dylint`, with the records sent to `<records>` and `{{ config_root }}`
# read as the tree. The lint groups read their tables from it
# (`answer_totality` its presenters and productions, `embedded_source` its
# types), and a crate expects their refusals. A run with no tables leaves
# each expectation unfulfilled, and the records do not build (#6838).
#
# With `--flags`, it prints that task's `DYLINT_RUSTFLAGS` in its place.
#
# Usage: policy.bash [--flags] <tree> <records>
# Exits 2 when the tree's `check:dylint` holds no such setting.
set -euo pipefail
flags=false
if [[ ${1:-} == --flags ]]; then flags=true; shift; fi
tree=${1:?usage: policy.bash [--flags] <tree> <records>}
records=${2:?usage: policy.bash [--flags] <tree> <records>}
tasks=$tree/.config/mise/tasks/mise-tasks-check.toml
if [[ $flags == true ]]; then
  awk -F'"' '$1 == "env.DYLINT_RUSTFLAGS = " { print $2; found = 1; exit } END { exit found ? 0 : 1 }' "$tasks" \
    || { echo "check:deletes: $tasks holds no env.DYLINT_RUSTFLAGS of check:dylint" >&2; exit 2; }
  exit 0
fi
# The setting is a TOML multi-line literal string, so its lines hold no
# escape: they are read as they stand, between the two `'''` lines.
awk -v records="$records" -v tree="$tree" -v quote="'''" '
  $0 == "env.DYLINT_TOML = " quote { on = 1; next }
  on && $0 == quote { found = 1; exit }
  on {
    if ($0 ~ /^evidence_directory = /) $0 = "evidence_directory = \"" records "\""
    while ((at = index($0, "{{ config_root }}")) > 0) $0 = substr($0, 1, at - 1) tree substr($0, at + 17)
    print
  }
  END { exit found ? 0 : 1 }' "$tasks" \
  || { echo "check:deletes: $tasks holds no env.DYLINT_TOML of check:dylint" >&2; exit 2; }
