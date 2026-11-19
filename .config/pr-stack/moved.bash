#!/usr/bin/env bash
# The act after a push that moves the trunk from outside the merge queue
# (#6700): `trunk_moved` restacks each open stack onto the new tip. The
# landing rebase runs it after its push (`.config/landing/rebase.bash`), and
# `mise run landing:moved` runs it after a push by hand: a hold or a repair.
#
# A restack that stops leaves its stack as it was. The act then pages the
# seat of each lane the stack holds, and the coordinator, with the reason:
# the conflicting files, or the refusal (`page_stopped`, `page.bash`).
#
# Exits 3 when a restack stops, 1 when a reading fails, and 0 otherwise.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
# shellcheck source=../gh/repo.bash
source "$here/../gh/repo.bash"
repo=$(repo_name)
# shellcheck source=stack.bash
source "$here/stack.bash"
trap drop_scratch EXIT
status=0
out=$(trunk_moved) || status=$?
[[ -z $out ]] || printf '%s\n' "$out"
(( status != 1 )) || exit 1
page_stopped <<< "$out"
exit "$status"
