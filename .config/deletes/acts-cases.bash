#!/usr/bin/env bash
# The cases of `acts.bash` (#7058), run by `check:deletes`. A scratch
# repository moves the items of one module to another, and the cases read
# the act that the comparison gives each item that leaves:
#   - a move that changes the visibility, the comments, the lines and a
#     module path before a name reads as `moved`;
#   - a move that changes the name alone reads as `renamed`;
#   - a move of a body that holds a `use` line and a longer path reads as
#     `moved`, and so does a test;
#   - a body that changes, an item that stands nowhere, an item whose twin is
#     a test, and an item whose twin the base already holds read as deleted;
#   - an item whose file is null reads as deleted, and never stops the run;
#   - of two getters whose bodies read alike once their names are set aside,
#     each takes the one of the head whose path ends as its own path ends;
#   - a move that adds `#[inline]` and changes the reason of a lint level in
#     a `cfg_attr` reads as `moved`, and a move that adds `#[cfg(test)]`
#     reads as deleted;
#   - a helper of a test module whose twin is an item of a fixture module
#     reads as `moved` (#7103), and an item whose twin is a test still reads
#     as deleted.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-deletes-acts.XXXXXX")
trap 'rm -rf "$work"' EXIT
failed=0
# A case that fails: its name, then what it wants and what it got.
fail() {
  printf 'deletes acts case FAILED: %s\n  want: %s\n  got:  %s\n' "$1" "$2" "$3"
  failed=1
}

repo=$work/repo
mkdir -p "$repo/crates/k/src"
git -C "$repo" init --quiet
git -C "$repo" config user.email cases@example.invalid
git -C "$repo" config user.name cases
git -C "$repo" config commit.gpgsign false
cat > "$repo/crates/k/src/a.rs" << 'EOF'
pub fn shift(x: u32) -> u32 {
    x + 1
}
pub struct Pair { left: u32, right: u32 }
pub fn path() -> u32 {
    crate::a::shift(1)
}
pub fn changed(x: u32) -> u32 { x * 2 }
pub fn gone() {}
fn helper() { assert!(true) }
#[test]
fn holds() { assert_eq!(super::shift(1), 2) }
pub fn left(&self) -> u32 { self.left }
pub fn right(&self) -> u32 { self.right }
#[cfg_attr(dylint_lib = "q", expect(lint, reason = "a"))]
pub fn guarded() -> u32 { 7 }
pub fn gated() -> u32 { 8 }
fn seed() -> u32 { 9 }
EOF
printf 'pub fn idle() {}\n' > "$repo/crates/k/src/c.rs"
git -C "$repo" add -A && git -C "$repo" commit --quiet --no-verify -m base
base=$(git -C "$repo" rev-parse HEAD)
git -C "$repo" rm --quiet crates/k/src/a.rs
cat > "$repo/crates/k/src/b.rs" << 'EOF'
// The shift moves here.
pub(crate) fn shift(x: u32) -> u32 { x + 1 } // on one line now
pub struct Couple { left: u32, right: u32 }
pub fn path() -> u32 {
    use crate::b::shift;
    crate::b::shift(1)
}
pub fn changed(x: u32) -> u32 { x * 3 }
#[test]
fn helper() { assert!(true) }
#[test]
fn holds() { assert_eq!(super::shift(1), 2) }
pub fn left(&self) -> u32 { self.left }
pub fn right(&self) -> u32 { self.right }
#[inline]
#[cfg_attr(dylint_lib = "q", expect(lint, reason = "b"))]
pub fn guarded() -> u32 { 7 }
#[cfg(test)]
pub fn gated() -> u32 { 8 }
pub fn seed() -> u32 { 9 }
EOF

item() { jq -n -c --arg id "$1" --arg kind "$2" --arg file "$3" --argjson start "$4" --argjson end "$5" --argjson test "${6:-false}" \
  '{id: $id, kind: $kind, file: (if $file == "" then null else $file end), start: $start, end: $end, test: $test}'; }
{
  item k::a::shift fn crates/k/src/a.rs 1 3
  item k::a::Pair struct crates/k/src/a.rs 4 4
  item k::a::path fn crates/k/src/a.rs 5 7
  item k::a::changed fn crates/k/src/a.rs 8 8
  item k::a::gone fn crates/k/src/a.rs 9 9
  item k::a::helper fn crates/k/src/a.rs 10 10
  item k::a::tests::holds fn crates/k/src/a.rs 12 12 true
  item k::a::Span::left fn crates/k/src/a.rs 13 13
  item k::a::Span::right fn crates/k/src/a.rs 14 14
  item k::a::guarded fn crates/k/src/a.rs 15 16
  item k::a::gated fn crates/k/src/a.rs 17 17
  item k::a::tests::seed fn crates/k/src/a.rs 18 18 true
  item k::a::written fn '' 1 1
  item k::c::idle fn crates/k/src/c.rs 1 1
} | jq -s -c . > "$work/base.json"
{
  item k::b::shift fn crates/k/src/b.rs 2 2
  item k::b::Couple struct crates/k/src/b.rs 3 3
  item k::b::path fn crates/k/src/b.rs 4 7
  item k::b::changed fn crates/k/src/b.rs 8 8
  item k::b::tests::helper fn crates/k/src/b.rs 10 10 true
  item k::b::tests::holds fn crates/k/src/b.rs 12 12 true
  item k::b::Span::left fn crates/k/src/b.rs 13 13
  item k::b::Span::right fn crates/k/src/b.rs 14 14
  item k::b::guarded fn crates/k/src/b.rs 15 17
  item k::b::gated fn crates/k/src/b.rs 18 19
  item k::fixture::seed fn crates/k/src/b.rs 20 20
  item k::b::written fn '' 1 1
  item k::c::idle fn crates/k/src/c.rs 1 1
} | jq -s -c . > "$work/head.json"

got=$(cd "$repo" && "$here/acts.bash" "$base" "$work/base.json" "$work/head.json" | jq -S -c .)
want=$(jq -n -S -c '{
  "k::a::shift": {act: "moved", at: "k::b::shift"},
  "k::a::Pair": {act: "renamed", at: "k::b::Couple"},
  "k::a::path": {act: "moved", at: "k::b::path"},
  "k::a::tests::holds": {act: "moved", at: "k::b::tests::holds"},
  "k::a::Span::left": {act: "moved", at: "k::b::Span::left"},
  "k::a::Span::right": {act: "moved", at: "k::b::Span::right"},
  "k::a::guarded": {act: "moved", at: "k::b::guarded"}}')
if [[ $(jq -S -c 'del(.["k::a::tests::seed"])' <<< "$got") != "$want" ]]; then
  fail "#7058: the acts of the items that leave" "$want" "$got"
fi
# The helper's flag is a test at the base and an item at the head; the
# item `helper`, whose twin is a test, stays out of the acts above.
seed=$(jq -S -c '.["k::a::tests::seed"]' <<< "$got")
if [[ $seed != '{"act":"moved","at":"k::fixture::seed"}' ]]; then
  fail "#7103: a helper of a test module reads as moved into an item of a fixture module" '{"act":"moved","at":"k::fixture::seed"}' "$seed"
fi

(( failed == 0 )) || exit 1
echo "deletes acts OK: a move reads as moved across the visibility, the comments, the lines, a use line and a module path; a new name reads as renamed; two getters alike take their own places; a test helper reads as moved into a fixture item; a changed body, an item that stands nowhere, a twin that is a test, a twin that the base holds and an item with no file read as deleted"
