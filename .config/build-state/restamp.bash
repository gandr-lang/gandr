#!/usr/bin/env bash
# A build state's sources, recorded and restamped (#3206), run by
# `check:build-state` over the cases in `restamp.json`. Each case builds a
# scratch repository of `a/x`, `a/y` and `b/c/z`, records its sources into
# `target/` as an archived state would, then applies the case's `change` as
# the next commit: `none`, `modify` (`a/x`), `add` (`a/w`), `remove` (`a/y`),
# `dirty` (`a/x` changed in the working tree while recording, then restored)
# or `unrecorded` (no record survives). The checkout's dates are then made
# fresh, as a clone's are, and the record restamped. The case's `output`
# lists every path still dated now, sorted: what a build script watching it
# would read as changed.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
source "$here/sources.bash"
cases=$here/restamp.json
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-restamp.XXXXXX")
trap 'rm -rf "$work"' EXIT
failed=0

identity() { git config user.name case && git config user.email case@example.invalid && git config commit.gpgsign false; }
write() { mkdir -p "${1%/*}" && printf '%s\n' "$2" > "$1"; }

count=$(jq length "$cases")
for (( i = 0; i < count; i++ )); do
  name=$(jq -r ".[$i].name" "$cases")
  change=$(jq -r ".[$i].change" "$cases")
  expected=$(jq -c ".[$i].output" "$cases")
  dir=$work/$i
  git init --quiet "$dir"
  cd "$dir"
  identity
  printf 'target/\n' > .git/info/exclude
  write a/x x && write a/y y && write b/c/z z
  git add . && git commit --quiet --message base
  [[ $change == dirty ]] && write a/x dirty
  sources_record target/debug
  [[ $change == dirty ]] && git checkout --quiet -- a/x
  case $change in
    modify) write a/x changed && git add a/x ;;
    add) write a/w added && git add a/w ;;
    remove) git rm --quiet a/y ;;
    unrecorded) rm target/debug/$SOURCES_RECORD ;;
  esac
  git diff --cached --quiet || git commit --quiet --message next
  # A clone's checkout: every path dated now.
  find . -path ./.git -prune -o -path ./target -prune -o -mindepth 1 -exec touch -h {} +
  records=()
  [[ -e target/debug/$SOURCES_RECORD ]] && records=(target/debug/"$SOURCES_RECORD")
  sources_restamp "${records[@]}"
  actual=$(find . -path ./.git -prune -o -path ./target -prune -o -mindepth 1 -printf '%T@ %P\n' |
    awk -v epoch="$SOURCES_EPOCH" 'int($1) != epoch { print $2 }' | sort | jq -R . | jq -sc .)
  if [[ $actual != "$expected" ]]; then
    printf 'build-state restamp case %s\n  expected: %s\n  actual:   %s\n' "$name" "$expected" "$actual" >&2
    failed=1
  fi
done
(( failed == 0 )) || exit 1
echo "build-state restamp OK: $count cases date only the sources a state was built from"
