#!/usr/bin/env bash
# The syntax ledger's gate, run by `check:syntax-ledger` once per case in
# `syntax-cases.json`: the ledger is regenerated into a temporary directory by
# `ledger:syntax`, the task a stale ledger names, under the case's
# environment, and compared with the committed `ledger/syntax.md` and
# `ledger/syntax.json` byte for byte. A case whose selection names a
# toolchain no host carries fails a task that consults the selection, and
# would write the default toolchain's grammar in a worktree (#4500).
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
cases=$here/syntax-cases.json
fresh=$(mktemp -d)
trap 'rm -rf "$fresh"' EXIT
failed=0
fail() {
  printf 'syntax ledger: %s\n' "$*" >&2
  failed=1
}

count=$(jq length "$cases")
for (( i = 0; i < count; i++ )); do
  name=$(jq -r ".[$i].name" "$cases")
  mapfile -t environment < <(jq -r ".[$i].environment | to_entries[] | \"\(.key)=\(.value)\"" "$cases")
  mkdir "$fresh/$i"
  if ! env "${environment[@]}" mise run --quiet ledger:syntax "$fresh/$i" > "$fresh/$i.out" 2>&1; then
    fail "$name: the regeneration fails: $(< "$fresh/$i.out")"
    continue
  fi
  for file in syntax.md syntax.json; do
    diff -u "ledger/$file" "$fresh/$i/$file" || fail "$name: ledger/$file is not the grammar's; run \`mise run ledger:syntax\`"
  done
done
(( failed == 0 )) || exit 1
echo "syntax ledger check OK: the committed ledger is the grammar's"
