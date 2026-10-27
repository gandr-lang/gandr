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
# would read as changed. A case with `"tools": "bsd"` runs the restamp and
# the reading under `xargs`, `touch` and `find` that refuse the GNU-only
# options macOS's lack, as a macOS checkout runs them (#3244).
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
source "$here/sources.bash"
cases=$here/restamp.json
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-restamp.XXXXXX")
trap 'rm -rf "$work"' EXIT
failed=0

identity() { git config user.name case && git config user.email case@example.invalid && git config commit.gpgsign false; }
write() { mkdir -p "${1%/*}" && printf '%s\n' "$2" > "$1"; }

# The BSD tools: each refuses an option only GNU's takes, by name, and runs
# the host's tool otherwise.
bsd=$work/bsd
mkdir -p "$bsd"
shim() {
  local tool=$1 refused=$2
  printf '#!/usr/bin/env bash\nfor arg; do [[ $arg =~ %s ]] && { echo "%s: invalid option $arg" >&2; exit 1; }; done\nexec %q "$@"\n' \
    "$refused" "$tool" "$(command -v "$tool")" > "$bsd/$tool"
  chmod +x "$bsd/$tool"
}
shim xargs '^(-d|-r|--.+)'
shim touch '^(-d|--.+)'
shim find '^-printf$'

# Every path under the checkout dated after SOURCES_STAMP, sorted, as JSON.
undated() {
  find . -path ./.git -prune -o -path ./target -prune -o -mindepth 1 -newer "$work/stamp" -print |
    awk '{ sub(/^\.\//, ""); print }' | sort | jq -R . | jq -sc .
}
TZ=UTC0 touch -t "$SOURCES_STAMP" "$work/stamp"

count=$(jq length "$cases")
for (( i = 0; i < count; i++ )); do
  name=$(jq -r ".[$i].name" "$cases")
  change=$(jq -r ".[$i].change" "$cases")
  tools=$(jq -r ".[$i].tools // \"host\"" "$cases")
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
  path=$PATH
  [[ $tools == bsd ]] && path=$bsd:$PATH
  if ! PATH=$path sources_restamp "${records[@]}"; then
    printf 'build-state restamp case %s: the restamp failed\n' "$name" >&2
    failed=1
    continue
  fi
  actual=$(PATH=$path undated)
  if [[ $actual != "$expected" ]]; then
    printf 'build-state restamp case %s\n  expected: %s\n  actual:   %s\n' "$name" "$expected" "$actual" >&2
    failed=1
  fi
done
(( failed == 0 )) || exit 1
echo "build-state restamp OK: $count cases date only the sources a state was built from"
