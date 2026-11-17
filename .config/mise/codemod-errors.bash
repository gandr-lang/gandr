#!/usr/bin/env bash
# The codemod of the errors' wave (#7385): each boxed `dyn Error` of a test
# takes the test's own `Failure`, a closed enum of the errors that the test
# propagates. The task `codemod:errors` runs it over `crates`, and the rules
# live in `.config/ast-grep/errors`. The compiler's errors that stay are the
# wave's second phase: each `From` that a `Failure` lacks, and each import.
#
# The rules run only on the files that hold a boxed error, so no other import
# of `Error` changes. A source file takes the rules of the type and the rule
# of the import in its `tests` module. A file under `tests/` takes the rules
# of the type and the rule of its own import. The task prints the files it
# rewrites and the count of `dyn Error` before and after.
set -euo pipefail
export LC_ALL=C

config=.config/ast-grep/errors/sgconfig.yml
types='boxed-error-is-failure|boxed-error-from-is-failure-from'
# The count of `dyn Error` in the crates' Rust sources.
count() {
  git grep -c -E 'dyn +((core|std)::error::)?Error\b' -- 'crates/*.rs' | awk -F: '{ total += $2 } END { print total + 0 }'
}

mapfile -t files < <(git grep -l -E 'Box(::)?<dyn ((core|std)::error::)?Error>' -- 'crates/*.rs')
sources=()
tests=()
for file in "${files[@]}"; do
  if [[ $file == crates/*/tests/* ]]; then tests+=("$file"); else sources+=("$file"); fi
done
before=$(count)
if (( ${#sources[@]} > 0 )); then
  ast-grep scan --config "$config" --filter "^($types|test-module-imports-failure)\$" --update-all "${sources[@]}"
fi
if (( ${#tests[@]} > 0 )); then
  ast-grep scan --config "$config" --filter "^($types|test-target-imports-failure)\$" --update-all "${tests[@]}"
fi
cargo fmt --all
printf 'codemod:errors: %d source files and %d files under tests/; dyn Error %d before, %d after\n' \
  "${#sources[@]}" "${#tests[@]}" "$before" "$(count)"
