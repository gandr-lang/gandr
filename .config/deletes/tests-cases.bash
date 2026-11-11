#!/usr/bin/env bash
# The cases of `tests.bash` and `paths.jq`, run by `check:deletes`. A module
# that a `#[path]` attribute places records its file with `..`, and
# `git show <rev>:<path>` does not resolve `..`. The check once read that
# failure as an empty text before, so 11 tests of `path_universe` that
# pull request 6843 does not touch read as changed (#6844). The cases build
# a scratch repository with a test in such a module. Its path in the tree
# reads as unchanged, a change to its lines reads as changed, and a path
# that the base does not hold stops the run with exit 2. A relative path
# that leaves the tree is refused. A source that a build script writes
# under the target directory has no path in the tree and is not compared.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-deletes-tests.XXXXXX")
trap 'rm -rf "$work"' EXIT
failed=0
fail() {
  echo "deletes tests case FAILED: $1"
  echo "  got: $2"
  failed=1
}

for pair in \
  'crates/kernel-core/src/path_universe/../higher_field/certificate_tests.rs crates/kernel-core/src/higher_field/certificate_tests.rs' \
  'crates/kernel-core/src/path_universe/../identity_recursion/universe_tests.rs crates/kernel-core/src/identity_recursion/universe_tests.rs' \
  'crates/kernel-core/src/path_universe/../identity_recursion/recursive/transport_tests.rs crates/kernel-core/src/identity_recursion/recursive/transport_tests.rs' \
  'crates/k/src/./a//b.rs crates/k/src/a/b.rs' \
  'crates/k/tests/lib.rs crates/k/tests/lib.rs'; do
  read -r raw want <<< "$pair"
  got=$(jq -rn -L "$here" --arg path "$raw" 'include "paths"; $path | tree_path')
  [[ $got == "$want" ]] || fail "#6844: the path in the tree of $raw is $want" "$got"
done
raw=crates/../../outside.rs
status=0
got=$(jq -rn -L "$here" --arg path "$raw" 'include "paths"; $path | tree_path' 2>&1) || status=$?
(( status != 0 )) && [[ $got == *"$raw leaves the tree"* ]] \
  || fail "#6844: the path $raw leaves the tree, and it is refused" "status $status, $got"
raw=/work/target/debug/build/gandr-runtime-emitter/884ab21cf6c1130e/out/stencils.rs
got=$(jq -rn -L "$here" --arg path "$raw" 'include "paths"; $path | tree_path')
[[ $got == null ]] || fail "#6844: a source that a build script writes, $raw, has no path in the tree" "$got"

repo=$work/repo
mkdir -p "$repo/crates/k/src/a" "$repo/crates/k/src/b"
git -C "$repo" init --quiet
git -C "$repo" config user.email cases@example.invalid
git -C "$repo" config user.name cases
printf '#[path = "../b/t.rs"]\nmod placed;\n' > "$repo/crates/k/src/a/tests.rs"
printf '#[test]\nfn holds()\n{\n    assert!(true);\n}\n' > "$repo/crates/k/src/b/t.rs"
printf 'pub fn other() {}\n' > "$repo/crates/k/src/lib.rs"
git -C "$repo" add -A && git -C "$repo" commit --quiet --no-verify -m base
base=$(git -C "$repo" rev-parse HEAD)
raw=crates/k/src/a/../b/t.rs
items() { jq -n -c -L "$here" --arg file "$1" --arg form "$2" 'include "paths"; [{id: "k::a::tests::placed::holds", kind: "fn", file: ($file | if $form == "tree" then tree_path else . end), start: 1, end: 5, test: true}]'; }
items "$raw" tree > "$work/normal.json"
items "$raw" raw > "$work/raw.json"
items /work/target/debug/build/k/0/out/t.rs tree > "$work/generated.json"

printf 'pub fn other() { let _ = 1; }\n' > "$repo/crates/k/src/lib.rs"
got=$(cd "$repo" && "$here/tests.bash" "$base" "$work/normal.json" "$work/normal.json")
[[ $got == '[]' ]] || fail "#6844: a test in a #[path] module whose file the change does not touch reads as unchanged" "$got"

status=0
got=$(cd "$repo" && "$here/tests.bash" "$base" "$work/raw.json" "$work/raw.json" 2> "$work/err") || status=$?
(( status == 2 )) && grep -qF "holds no $raw" "$work/err" \
  || fail "#6844: a file that the base does not hold stops the run with exit 2, and never reads as a change" "status $status, $got, $(< "$work/err")"

printf '#[test]\nfn holds()\n{\n    assert!(1 + 1 == 2);\n}\n' > "$repo/crates/k/src/b/t.rs"
got=$(cd "$repo" && "$here/tests.bash" "$base" "$work/normal.json" "$work/normal.json")
[[ $got == '[{"id":"k::a::tests::placed::holds","name":"holds"}]' ]] \
  || fail "#6844: a change to the lines of a test in a #[path] module reads as changed" "$got"

got=$(cd "$repo" && "$here/tests.bash" "$base" "$work/generated.json" "$work/generated.json")
[[ $got == '[]' ]] || fail "#6844: a test in a source that a build script writes is not compared, and never stops the run" "$got"

(( failed == 0 )) || exit 1
echo "deletes tests OK: a #[path] test reads at its path in the tree, unchanged when untouched and changed when edited; a path the base lacks stops the run, a path that leaves the tree is refused, and a written source is not compared"
