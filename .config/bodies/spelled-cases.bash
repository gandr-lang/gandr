#!/usr/bin/env bash
# The issues that a `spelling: replaces` line cites (#7138, `spelled.bash`),
# run by `check:claims`. A body with no such line gives nothing and exits 0,
# so `pr:open` goes on. A line that cites two issues, one of them twice,
# gives each once.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
dir=$(mktemp -d)
trap 'rm -rf "$dir"' EXIT
failed=0

fail() {
  echo "spelled case FAILED: $1"
  echo "  got: $2"
  failed=1
}

printf 'Closes #7.\n' > "$dir/none.md"
got=$("$here/spelled.bash" "$dir/none.md") || got="exit $?"
[[ -z $got ]] || fail "#7138: a body with no spelling line gives nothing and exits 0" "$got"

printf 'Closes #7.\n\n- spelling: replaces `a` (#34) and `b` (#12, #34)\n' > "$dir/two.md"
got=$("$here/spelled.bash" "$dir/two.md" | paste -sd ' ' -) || got="exit $?"
[[ $got == '12 34' ]] || fail "#7138: a spelling line that cites two issues gives each once" "$got"

(( failed == 0 )) || exit 1
echo "spelled check OK: a body with no spelling line gives nothing and exits 0, and a line that cites two issues gives each once"
