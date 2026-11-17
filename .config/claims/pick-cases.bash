#!/usr/bin/env bash
# The pick `claim:next` reads from `next.jq`'s answer (#5178, `pick.bash`),
# run by `check:claims`.
set -euo pipefail
source "$(cd "${BASH_SOURCE[0]%/*}" && pwd)/pick.bash"
failed=0

fail() {
  echo "pick case FAILED: $1"
  echo "  got: $2"
  failed=1
}

got=$(printf 'held: #5165 fix(surface): a labelled let pattern\nobservation due: #4884 — mise run debug:test <package> <test>\n4884\tfocus\tweb-targets: providers ahead of time\n' | claim_pick)
[[ $got == $'4884\tfocus\tweb-targets: providers ahead of time' ]] || fail "#5178: a held line before the pick leaves the pick" "$got"

got=$(printf 'held: #5165 fix(surface): a labelled let pattern\nheld: #5147 refactor(core): generalise\n' | claim_pick)
[[ -z $got ]] || fail "#5178: held lines alone give no pick" "$got"

(( failed == 0 )) || exit 1
echo "pick check OK: 2 cases read as recorded"
