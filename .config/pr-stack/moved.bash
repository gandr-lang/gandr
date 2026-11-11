#!/usr/bin/env bash
# The act after a push that moves the trunk from outside the merge queue
# (#6700): `trunk_moved` restacks each open stack onto the new tip. The
# landing rebase runs it after its push (`.config/landing/rebase.bash`), and
# `mise run landing:moved` runs it after a push by hand: a hold or a repair.
#
# A restack that stops leaves its stack as it was. The act then pages the
# seat of each lane the stack holds, and the coordinator, with the reason:
# the conflicting files, or the refusal. It pages through `stall:watch`'s
# configuration (`page`: the command, the coordinator, each lane's seat and
# the triage seat for a lane with none). With no such configuration it
# prints the page on stderr alone.
#
# Exits 3 when a restack stops, 1 when a reading fails, and 0 otherwise.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
# shellcheck source=../gh/repo.bash
source "$here/../gh/repo.bash"
repo=$(repo_name)
# shellcheck source=stack.bash
source "$here/stack.bash"
# shellcheck source=../stall/stall.bash
source "$here/../stall/stall.bash"
trap drop_scratch EXIT
status=0
out=$(trunk_moved) || status=$?
[[ -z $out ]] || printf '%s\n' "$out"
(( status != 1 )) || exit 1
page=$(stall_configuration | jq -c '.page // empty')
while IFS= read -r line; do
  [[ $line == stopped\ * ]] || continue
  text="STACK $line"
  if [[ -z $page ]]; then
    echo "no page configuration reaches the seats: $text" >&2
    continue
  fi
  mapfile -t command < <(jq -r '.command[]' <<< "$page")
  mapfile -t coordinator < <(jq -r '.coordinator[]' <<< "$page")
  lanes=${line#*[}
  lanes=${lanes%%]*}
  for lane in $lanes; do
    mapfile -t seat < <(jq -r --arg lane "$lane" '(.seats[$lane] // .triage)[]' <<< "$page")
    "${command[@]}" "${seat[@]}" "$text" || echo "the page to lane $lane is not delivered: $text" >&2
  done
  "${command[@]}" "${coordinator[@]}" "$text" || echo "the page to the coordinator is not delivered: $text" >&2
done <<< "$out"
exit "$status"
