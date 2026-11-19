#!/usr/bin/env bash
# The cases of `counts.bash` (#8152), run by `check:recovery-counts`. Each case
# commits a base and a head in a scratch repository. A stub stands for
# `ledger:recovery`: it prints the line of `counts.txt` in the tree it runs in.
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
source "$here/../cases/scratch.bash"
counts=$here/counts.bash
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
fail() {
  echo "recovery-counts: $*" >&2
  exit 1
}
stub=$work/ledger.bash
printf '#!/usr/bin/env bash\ncat counts.txt\n' > "$stub"
chmod +x "$stub"
export RECOVERY_LEDGER=$stub
line_base='100 mutants swept: 80 marked where they were made, 5 accepted, 5 well formed, 5 closed early, 5 marked elsewhere'
line_same='100 mutants swept: 80 marked where they were made, 6 accepted, 4 well formed, 5 closed early, 5 marked elsewhere'
line_fall='100 mutants swept: 78 marked where they were made, 7 accepted, 5 well formed, 5 closed early, 5 marked elsewhere'
# A repository whose base holds `line_base` and whose head holds `$1`, with a
# change under `$2`.
repository() {
  local repo=$work/repo
  rm -rf "$repo"
  git init --quiet "$repo"
  identity "$repo"
  printf '%s\n' "$line_base" > "$repo/counts.txt"
  mkdir -p "$repo/crates/surface-parser" "$repo/docs"
  echo a > "$repo/crates/surface-parser/a.rs"
  echo a > "$repo/docs/a.md"
  git -C "$repo" add -A
  git -C "$repo" commit --quiet -m base
  git -C "$repo" tag base
  printf '%s\n' "$1" > "$repo/counts.txt"
  echo b > "$repo/$2"
  git -C "$repo" add -A
  git -C "$repo" commit --quiet -m head
  echo "$repo"
}
body() {
  printf '### Recovery\n\n- base: %s\n- head: %s\n%s\n' "$1" "$2" "${3:-}" > "$work/body.md"
  echo "$work/body.md"
}
run() {
  local repo=$1 body=$2 status=0
  (cd "$repo" && "$counts" base "$body") > "$work/out" 2>&1 || status=$?
  echo "$status"
}
repo=$(repository "$line_fall" docs/a.md)
[[ $(run "$repo" "$work/none.md") == 0 ]] || fail "#8152: a change outside the parser was refused: $(cat "$work/out")"
repo=$(repository "$line_same" crates/surface-parser/a.rs)
[[ $(run "$repo" "$(body "$line_base" "$line_same")") == 0 ]] || fail "#8152: the stated counts were refused: $(cat "$work/out")"
repo=$(repository "$line_same" crates/surface-parser/a.rs)
[[ $(run "$repo" "$(body "$line_base" "$line_base")") == 2 ]] || fail "#8152: other counts passed: $(cat "$work/out")"
grep -q "^- head: $line_same$" "$work/out" || fail "#8152: the refusal names no line to write: $(cat "$work/out")"
repo=$(repository "$line_fall" crates/surface-parser/a.rs)
[[ $(run "$repo" "$(body "$line_base" "$line_fall")") == 2 ]] || fail "#8152: a fall of two points passed: $(cat "$work/out")"
grep -q 'falls 2.00 points' "$work/out" || fail "#8152: the refusal names no fall: $(cat "$work/out")"
repo=$(repository "$line_fall" crates/surface-parser/a.rs)
[[ $(run "$repo" "$(body "$line_base" "$line_fall" '- fall: admitted by the owner, #8152')") == 0 ]] \
  || fail "#8152: a fall that the owner admits was refused: $(cat "$work/out")"
echo "recovery-counts check OK: a change outside the parser passes, stated counts pass, other counts are refused with the lines to write, a fall of two points is refused, and a fall that the owner admits passes"
