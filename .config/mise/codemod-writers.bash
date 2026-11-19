#!/usr/bin/env bash
# The codemod of the writers' and consoles' wave. Each `dyn io::Write` and
# `dyn fmt::Display` behind a reference in a function's parameter takes
# `impl`. Then the function is generic over its writer or its value. Each
# `dyn Console` there takes `Streams<'_>`, the closed set of the known
# consoles.
# - see: #7387, `.config/ast-grep/writers`
#
# The task `codemod:writers` runs it over `crates`. The sites that stay are
# the wave's second phase: a closure's parameter, a field, and an array of
# values of different types. The task prints the count of the wave's sites
# before and after.
set -euo pipefail
export LC_ALL=C

config=.config/ast-grep/writers/sgconfig.yml
pattern='dyn +((core|std)::)?((io|fmt)::)?(Write|Display)\b|dyn +([A-Za-z_]+::)*Console\b'
# The count of the wave's sites in the crates' Rust sources.
count() {
  git grep -o -E "$pattern" -- 'crates/*.rs' | awk 'END { print NR }'
}

mapfile -t files < <(git grep -l -E "$pattern" -- 'crates/*.rs')
before=$(count)
if (( ${#files[@]} > 0 )); then
  ast-grep scan --config "$config" --update-all "${files[@]}"
fi
cargo fmt --all
printf 'codemod:writers: %d files hold a site; dyn Write, dyn Display and dyn Console %d before, %d after\n' \
  "${#files[@]}" "$before" "$(count)"
