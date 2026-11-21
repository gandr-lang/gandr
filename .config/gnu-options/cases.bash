#!/usr/bin/env bash
# The scanner refuses an unnoted GNU-only option and ignores a tool name used as data.
# - see: #8165
set -euo pipefail

here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
scratch=$(mktemp -d "${TMPDIR:-/tmp}/gandr-gnu-options.XXXXXX")
trap 'rm -rf "$scratch"' EXIT
failed=0

fail() {
  printf '%s\n' "$*" >&2
  failed=1
}

mkdir -p "$scratch/.config/gnu-options"
cp "$here/check.bash" "$here/table.json" "$scratch/.config/gnu-options/"
git init --quiet "$scratch"
git -C "$scratch" config user.email case@example.invalid
git -C "$scratch" config user.name case

printf '%s\n' 'find . -printf "%p\\n"' > "$scratch/.config/refused.bash"
git -C "$scratch" add .
status=0
output=$("$scratch/.config/gnu-options/check.bash" "$scratch" 2>&1) || status=$?
[[ $status == 1 && $output == *'.config/refused.bash:1: GNU-only option `find -printf`'* ]] \
  || fail "#8165: an unnoted GNU-only option is refused: $output"

rm "$scratch/.config/refused.bash"
printf '%s\n' '# gnu-only: the BSD form has no -printf option.' 'find . -printf "%p\\n"' \
  > "$scratch/.config/noted.bash"
printf '%s\n' "shim find '^-printf$'" > "$scratch/.config/false-hit.bash"
git -C "$scratch" add -A
status=0
output=$("$scratch/.config/gnu-options/check.bash" "$scratch" 2>&1) || status=$?
[[ $status == 0 ]] || fail "#8165: a direct note permits the use and data is not a use: $output"

(( failed == 0 )) || exit 1
printf 'gnu-options case OK: the scanner refuses an unnoted option and accepts one direct note\n'
