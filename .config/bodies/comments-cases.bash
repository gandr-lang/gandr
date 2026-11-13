#!/usr/bin/env bash
# The comment lines a change drops (#6004, `comments.bash`), read in a scratch
# repository and run by `check:claims`.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
repo=$(mktemp -d)
trap 'rm -rf "$repo"' EXIT
failed=0

fail() {
  echo "comments case FAILED: $1"
  echo "  got: $2"
  failed=1
}

git init --quiet --initial-branch=main "$repo"
git -C "$repo" config commit.gpgsign false
mkdir -p "$repo/crates/a/src" "$repo/crates/b/src"
printf '/// a fact the file keeps\nfn kept() {}\n' > "$repo/crates/a/src/gone.rs"
printf '/// a fact that moves\nfn moved() {}\n' > "$repo/crates/a/src/moved.rs"
git -C "$repo" add -A && git -C "$repo" commit --quiet --no-verify -m base
git -C "$repo" rm --quiet crates/a/src/gone.rs crates/a/src/moved.rs
printf '/// a fact that moves\nfn moved() {}\n' > "$repo/crates/b/src/moved.rs"
git -C "$repo" add -A && git -C "$repo" commit --quiet --no-verify -m head

got=$(cd "$repo" && "$here/comments.bash" HEAD~1 | jq -c 'sort_by(.path)')
[[ $got == '[{"path":"crates/a/src/gone.rs","removed":1,"dropped":1},{"path":"crates/a/src/moved.rs","removed":1,"dropped":0}]' ]] \
  || fail "#7084: a deleted file's comment lines read under its own path, and a line that moves is kept" "$got"

(( failed == 0 )) || exit 1
echo "comments check OK: 1 case reads as recorded"
