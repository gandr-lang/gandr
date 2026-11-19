#!/usr/bin/env bash
# The cases of `origin.bash`, run by `check:deletes`. The origin of a type once
# came from a field's bare name: `git log -S` over the word `start` found the
# commit of #990, which first wrote `start` in the file, where #6979 adds the
# type with both its fields (#7259). The cases build a scratch repository: a
# commit of #990 writes the word `start`, and the merge of #6979 brings in a
# commit with no number that adds `struct Segment` and its fields. The span
# of the type and the span of one field each name #6979, the word names
# #990, and a file names the pull request that adds it.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
source "$here/../cases/scratch.bash"
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-deletes-origin.XXXXXX")
trap 'rm -rf "$work"' EXIT
failed=0
expect() {
  local want=$1 got
  shift
  got=$(cd "$work/repo" && "$here/origin.bash" "$base" "$@")
  [[ $got == "$want" ]] || {
    echo "deletes origin case FAILED: $* names #$want"
    echo "  got: $got"
    failed=1
  }
}

repo=$work/repo
mkdir -p "$repo/crates/k/src"
git -C "$repo" init --quiet --initial-branch=landing
identity "$repo"
cd "$repo"
commit crates/k/src/arena.rs 'pub fn shift(start: usize) -> usize
{
    start + 1
}' 'feat(core): run transports (#990)'
git switch --quiet --create segments
commit crates/k/src/arena.rs 'pub fn shift(start: usize) -> usize
{
    start + 1
}

struct Segment
{
    start: usize,
    nodes: Vec<u8>,
}' 'feat(kernel): freeze a family by segments'
git switch --quiet landing
git merge --quiet --no-ff --no-edit --message 'feat(kernel): freeze by segments (#6979)' segments
base=$(git rev-parse HEAD)
cd "$here"

expect 6979 span crates/k/src/arena.rs 6 10
expect 6979 span crates/k/src/arena.rs 8 8
expect 990 text crates/k/src/arena.rs start
expect 990 file crates/k/src/arena.rs
expect null span crates/k/src/arena.rs 40 41
expect null file crates/k/src/absent.rs

(( failed == 0 )) || exit 1
echo "deletes origin cases OK: an item's own lines name its pull request, a field's bare name does not, and a merge names a commit with no number"
