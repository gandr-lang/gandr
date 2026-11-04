#!/usr/bin/env bash
# The stack top's hold over seats that race on one origin (#5122,
# `hold.bash`), run by `check:pr-stack` over the cases in `race.json`. Each
# case builds a scratch repository with a local bare origin: a base commit on
# `main`, the branch `lower` of the open pull request #1, and one clone for
# each seat of the case's `seats`, its branch `upper-<seat>` forked from
# `main` with one commit on a file of its own. The server's open pull
# requests are a file, and a gate is a line holding the tree it passed on.
# Each step of the case's `steps` is one seat's act:
# - `<seat> gate`: a gate passes on the seat's tree.
# - `<seat> open`: one `pr:open` run, in `pr:open`'s order: the hold, the
#   stacking on the top (`await_top`, `stack_on_top`), the gate's reading on
#   the stacked head, and the push, which opens the seat's pull request on
#   the top and releases the hold. A refusal for want of a gate keeps the
#   hold. The run ends as `pr:open` exits, so the next run reads the hold
#   from the server.
# - `<seat> lapse`: the seat's hold is written again with its deadline
#   passed, as a holder that crashed leaves it.
# - `<seat> drop`: the seat releases the last hold it wrote, as its run's exit
#   does once another seat took it over.
# - `<seat> race`: the seat writes the hold over no record, as each of two
#   seats that read no hold at once writes.
# The result is the steps' lines joined by `; `, compared with the case's
# `output`.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
source "$here/stack.bash"
cases=$here/race.json
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-race.XXXXXX")
trap 'rm -rf "$work"' EXIT
repo=case/case
trunk=main
failed=0

commit() { printf '%s\n' "$2" > "$1" && git add "$1" && git commit --quiet --message "$3"; }
identity() {
  git config user.name case
  git config user.email case@example.invalid
  git config commit.gpgsign false
}

# The scratch repository in `$1`, with a clone for each seat after it.
scenario() {
  local dir=$1 seat
  shift
  git init --quiet --bare --initial-branch=main "$dir/origin.git"
  git clone --quiet "$dir/origin.git" "$dir/seed" 2> /dev/null
  (
    cd "$dir/seed"
    identity
    commit f.txt a base
    git push --quiet origin main
    git switch --quiet --create lower
    commit l.txt l "lower's own"
    git push --quiet origin lower
  )
  echo '[{"number": 1, "head": "lower", "base": "main", "created": "1"}]' > "$dir/prs.json"
  : > "$dir/gates"
  for seat in "$@"; do
    git clone --quiet "$dir/origin.git" "$dir/$seat" 2> /dev/null
    (
      cd "$dir/$seat"
      identity
      git switch --quiet --create "upper-$seat" origin/main
      commit "$seat.txt" "$seat" "$seat's own"
    )
  done
}

# The server's open pull requests, as `open.jq` gives them.
open_prs() { jq -c 'map(. + {landing: false, held: false, bot: false, hold: null})' "$dir/prs.json"; }

# One `pr:open` run of seat `$1`, in its clone.
open_run() {
  local seat=$1 own=upper-$1 out status=0 on number
  # As `pr:open` calls it: in this shell, so the record it writes stays set.
  top_hold_take "$own" "$(git rev-parse HEAD)" > "$dir/take.$seat" 2>&1 || status=$?
  out=$(< "$dir/take.$seat")
  if (( status == 3 )) && [[ $out =~ held\ by\ \`([^\`]+)\` ]]; then
    echo "$seat waits on ${BASH_REMATCH[1]}"
    return
  fi
  (( status == 0 )) || { echo "$seat refused: $out"; return; }
  if [[ $out =~ hold\ by\ \`([^\`]+)\`\ passed ]]; then echo "$seat takes the hold over from ${BASH_REMATCH[1]}"; fi
  echo "$top_hold_sha" > "$dir/sha.$seat"
  stack_on_top "$own" "$(await_top "$own")" > /dev/null 2>&1 || { echo "$seat refused: the stacking failed"; top_hold_release; return; }
  on=main
  if [[ $stacked_top != null ]]; then on=$(jq -r .head <<< "$stacked_top"); fi
  if ! grep -qxF "$(git rev-parse 'HEAD^{tree}')" "$dir/gates"; then
    echo "$seat refused for a gate, stacked on $on and holding the top"
    return
  fi
  git push --quiet --force origin HEAD
  number=$(($(jq length "$dir/prs.json") + 1))
  jq -c --argjson n "$number" --arg head "$own" --arg base "$on" '. + [{number: $n, head: $head, base: $base, created: "\($n)"}]' \
    "$dir/prs.json" > "$dir/prs.next"
  mv "$dir/prs.next" "$dir/prs.json"
  top_hold_release
  echo "$seat opened #$number on $on"
}

# Seat `$1`'s act `$2`, in its clone and a process of its own.
act() {
  local seat=$1 own=upper-$1 hold
  cd "$dir/$seat"
  case $2 in
    gate)
      git rev-parse 'HEAD^{tree}' >> "$dir/gates"
      echo "$seat gates"
      ;;
    open) open_run "$seat" ;;
    lapse)
      hold=$(top_hold_reading)
      top_hold_seconds=-1
      top_hold_write "$own" "$(jq -r .head <<< "$hold")" "$(jq -r .began <<< "$hold")" "$(jq -r .sha <<< "$hold")"
      echo "$top_hold_sha" > "$dir/sha.$seat"
      echo "$seat's hold lapses"
      ;;
    drop)
      top_hold_sha=$(< "$dir/sha.$seat")
      top_hold_release
      echo "$seat drops the hold it wrote"
      ;;
    race)
      if top_hold_write "$own" "$(git rev-parse HEAD)" "$(date +%s)" ""; then
        echo "$seat writes the hold"
      else
        echo "$seat's write loses"
      fi
      ;;
  esac
}

count=$(jq length "$cases")
for (( i = 0; i < count; i++ )); do
  name=$(jq -r ".[$i].name" "$cases")
  expected=$(jq -r ".[$i].output" "$cases")
  mapfile -t seats < <(jq -r ".[$i].seats[]" "$cases")
  mapfile -t steps < <(jq -r ".[$i].steps[]" "$cases")
  dir=$work/$i
  mkdir "$dir"
  scenario "$dir" "${seats[@]}" > /dev/null
  lines=()
  for step in "${steps[@]}"; do
    while IFS= read -r line; do lines+=("$line"); done < <(act "${step% *}" "${step#* }" 2>&1)
  done
  actual=$(printf '%s; ' "${lines[@]}")
  actual=${actual%; }
  if [[ $actual != "$expected" ]]; then
    printf 'pr-stack race case %s\n  expected: %s\n  actual:   %s\n' "$name" "$expected" "$actual" >&2
    failed=1
  fi
done
(( failed == 0 )) || exit 1
echo "pr-stack race OK: $count cases hold the top as recorded"
