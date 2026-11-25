#!/usr/bin/env bash
# The Miri skip scanner works with a grep that refuses GNU-only options.
# - see: #8143
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
scratch=$(mktemp -d)
cleanup() {
  rm -rf "$scratch"
}
trap cleanup EXIT
failed=0
fail() {
  printf '%s\n' "$*" >&2
  failed=1
}
mkdir -p "$scratch/.config/unsafe" "$scratch/crates/fixture/src" "$scratch/bin"
git init --quiet "$scratch"
cp "$here/run.bash" "$scratch/.config/unsafe/run.bash"
cp "$here/skips.jq" "$scratch/.config/unsafe/skips.jq"
printf '%s\n' \
  '{"crates":[{"package":"fixture","path":"crates/fixture","skips":[{"test":"skipped","why":"the portable scanner holds one skip"}]}]}' \
  > "$scratch/.config/unsafe/crates.json"
printf '%s\n' \
  '#[cfg_attr(' \
  '    miri,' \
  '    ignore = "the portable scanner holds one skip"' \
  ')]' \
  'fn skipped() {}' \
  > "$scratch/crates/fixture/src/lib.rs"
printf '%s\n' \
  '#!/usr/bin/env bash' \
  'for argument in "$@"; do' \
  '  [[ $argument != *P* ]] || exit 2' \
  'done' \
  'exec /usr/bin/grep "$@"' \
  > "$scratch/bin/grep"
chmod +x "$scratch/bin/grep"
status=0
output=$(cd "$scratch" && PATH="$scratch/bin:$PATH" .config/unsafe/run.bash skips fixture 2>&1) || status=$?
[[ $status == 0 && $output == 'fixture: 1 skip(s), each a row of the list' ]] \
  || fail "#8143: the skip scanner calls no GNU-only grep option: $output"
(( failed == 0 )) || exit 1
echo "unsafe skips case OK: a grep without GNU options reads one multiline Miri skip"
