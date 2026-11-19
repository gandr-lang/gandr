#!/usr/bin/env bash
# The cases of `target-pin.bash` (#7497), over the real compiler and cargo. A
# scratch package pins the tree's toolchain, and cargo builds it once, so its
# target holds cargo's own record. A target that the tree's compiler filled
# stays. A record that names another compiler cleans the target, and the step
# names that compiler. A target with no record, or with a record that names
# no compiler, stays.
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
root=$(cd "$here/../.." && pwd)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
unset CARGO_TARGET_DIR
failed=0
fail() {
  printf 'target:pin case FAILED: %s\n  wanted: %s\n  got:    %s\n' "$1" "$2" "$3" >&2
  failed=1
}
# A package that pins the tree's toolchain, built once, with one more unit in
# its target that only a clean takes out.
package() {
  local dir=$scratch/$1
  mkdir -p "$dir/src"
  cp "$root/rust-toolchain.toml" "$dir/"
  printf '[package]\nname = "scratch"\nversion = "0.0.0"\nedition = "2024"\n' > "$dir/Cargo.toml"
  : > "$dir/src/lib.rs"
  (cd "$dir" && cargo build --quiet)
  : > "$dir/target/debug/unit"
  printf '%s\n' "$dir"
}
# The step in `$1`: its status, and whether the unit stays.
outcome() {
  local status=0
  (cd "$1" && "$here/target-pin.bash") 2> "$scratch/err" || status=$?
  if [[ -e $1/target/debug/unit ]]; then echo "exit $status, kept"; else echo "exit $status, cleaned"; fi
}
same=$(package same)
got=$(outcome "$same")
[[ $got == "exit 0, kept" ]] || fail "#7497: a target that the tree's compiler filled stays" "exit 0, kept" "$got"

other=$(package other)
jq '.outputs |= map_values(.stdout |= (strings | sub("commit-hash: [0-9a-f]+"; "commit-hash: 84b36a78a0000000000000000000000000000000") | sub("^rustc [^\n]*"; "rustc 1.99.0-nightly (84b36a78a 2026-08-06)")))' \
  "$other/target/.rustc_info.json" > "$scratch/record" && mv "$scratch/record" "$other/target/.rustc_info.json"
got=$(outcome "$other")
[[ $got == "exit 0, cleaned" ]] || fail "#7497: a target that another compiler filled is cleaned" "exit 0, cleaned" "$got"
named=$(< "$scratch/err")
[[ $named == *"rustc 1.99.0-nightly (84b36a78a 2026-08-06)"* ]] \
  || fail "#7497: the clean names the compiler that filled the target" "rustc 1.99.0-nightly (84b36a78a 2026-08-06)" "$named"

none=$(package none)
rm "$none/target/.rustc_info.json"
got=$(outcome "$none")
[[ $got == "exit 0, kept" ]] || fail "a target with no record stays" "exit 0, kept" "$got"

blank=$(package blank)
jq '.outputs = {}' "$blank/target/.rustc_info.json" > "$scratch/record" && mv "$scratch/record" "$blank/target/.rustc_info.json"
got=$(outcome "$blank")
[[ $got == "exit 0, kept" ]] || fail "a record that names no compiler keeps its target" "exit 0, kept" "$got"

(( failed == 0 )) || exit 1
echo "target:pin cases OK: 4 targets, one compiler kept, another cleaned and named, no record and an empty record kept"
