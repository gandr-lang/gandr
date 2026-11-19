#!/usr/bin/env bash
# The codemod of the callbacks' wave (#7386): each `dyn Fn` and `dyn FnMut`
# behind a reference in a function's parameter takes `impl`, so the function
# is generic over its callback. The task `codemod:callbacks` runs it over
# `crates`, and the rule lives in `.config/ast-grep/callbacks`. The sites that
# stay are the wave's second phase: a closure's parameter, a type alias, a
# field, and each object of a trait whose method turns generic. The task
# prints the count of `dyn Fn` and `dyn FnMut` before and after.
set -euo pipefail
export LC_ALL=C

config=.config/ast-grep/callbacks/sgconfig.yml
pattern='dyn +((core|std)::ops::)?Fn(Mut)?\b'
# The count of `dyn Fn` and `dyn FnMut` in the crates' Rust sources.
count() {
  git grep -o -E "$pattern" -- 'crates/*.rs' | awk 'END { print NR }'
}

mapfile -t files < <(git grep -l -E "$pattern" -- 'crates/*.rs')
before=$(count)
if (( ${#files[@]} > 0 )); then
  ast-grep scan --config "$config" --update-all "${files[@]}"
fi
cargo fmt --all
printf 'codemod:callbacks: %d files hold a site; dyn Fn and dyn FnMut %d before, %d after\n' \
  "${#files[@]}" "$before" "$(count)"
