# shellcheck shell=bash
# The page of a restack that stops (#6700, #6760), sourced by
# `landing:moved` (`moved.bash`) and `pr:open`. `page_stopped` reads the
# lines of `tip_restack` on stdin, and for each `stopped <number>…
# [<lane>…]: <the reason>` it pages the seat of each lane named, and the
# coordinator, with the line. It pages through `stall:watch`'s configuration
# (`page`: the command, the coordinator, each lane's seat and the triage
# seat for a lane with none). With no such configuration it prints the page
# on stderr alone.

# shellcheck source=../stall/stall.bash
source "$(git rev-parse --show-toplevel)/.config/stall/stall.bash"

page_stopped() {
  local page line text lanes lane
  local -a command coordinator seat
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
  done
}
