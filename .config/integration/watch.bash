# shellcheck shell=bash
# The head watcher of `landing` (#6587), sourced by `landing:watch`. Each
# interval it reads `landing` and `main` by `git fetch` alone. A new head
# of `landing` runs the landing's gate, `mise run check`, over the whole
# move since the last green head. A red check gets an owner: the search
# over the first parents (`search.jq`) names the first commit where it
# fails, GitHub names the pull request of that commit, and `owner.jq`
# writes the defect, the lane and the `FIX` page. Each interval also reads
# how long `main` stands behind `landing` (`gap.jq`), and a gap past
# `watch_limit` minutes pages the fixer once for each head of `main`.
#
# The gate runs in a clone of its own, `watch-landing` under the state
# directory, which borrows the objects of this checkout's repository. So
# the gate holds the lock of the lane `watch` and one of the host's gate
# slots (`.config/mise/gate.bash`), never a seat's lane. The clone reads
# `landing` and `main` into `refs/watch/`. Its `origin/landing` holds the
# last green head, so the gate reads the move since that head as its
# change, as `pr:open` reads a branch's change against its fork. A move of
# `landing` during a run waits for the run to end, and the next run checks
# the newest head alone.
#
# The watcher calls GitHub only for a red head: one read of the culprit's
# pull request, one read of the open `landing:` defects, and the writes of
# one defect, its claim and its page. A green head and an unmoved one call
# nothing.
#
# The state is `watch_state`: `green`, the last head where the gate passes;
# `checked`, the last head the gate ran on; `gap`, the last reading of the
# gap; and `paged`, the head of `main` at the last page of the gap.

watch_dir="$(git rev-parse --show-toplevel)/.config/integration"
watch_state="${XDG_STATE_HOME:-$HOME/.local/state}/gandr/landing-watch.json"
watch_tree="${XDG_STATE_HOME:-$HOME/.local/state}/gandr/watch-landing"
watch_limit=45
# shellcheck disable=SC2034 # `landing:watch` reads the interval
watch_interval=60
source "$watch_dir/../stall/stall.bash"

# The state, `{}` when there is none.
watch_memory() {
  if [[ -f "$watch_state" ]]; then jq -c . "$watch_state"; else echo '{}'; fi
}

# Writes the state `$1`.
watch_remember() {
  mkdir -p "$(dirname "$watch_state")"
  printf '%s\n' "$1" > "$watch_state.tmp"
  mv "$watch_state.tmp" "$watch_state"
}

# Makes the clone when it is absent, then reads `landing` and `main` into
# its `refs/watch/`.
watch_fetch() {
  if [[ ! -d "$watch_tree/.git" ]]; then
    mkdir -p "$(dirname "$watch_tree")"
    git clone --quiet --shared --no-checkout "$(git rev-parse --path-format=absolute --git-common-dir)" "$watch_tree"
    git -C "$watch_tree" remote set-url origin "$(git remote get-url origin)"
  fi
  git -C "$watch_tree" fetch --quiet origin '+refs/heads/landing:refs/watch/landing' '+refs/heads/main:refs/watch/main'
}

# Pages the seat of lane `$1` with the line `$2`, the triage seat for a
# lane with no seat, and the coordinator with the same line, through the
# page script of the stall detector's configuration.
watch_page() {
  local page
  local -a command seat coordinator
  page=$(stall_configuration | jq -c '.page // empty')
  [[ -n $page ]] || { echo "landing:watch: no page configuration; the line is: $2" >&2; return 1; }
  mapfile -t command < <(jq -r '.command[]' <<< "$page")
  mapfile -t seat < <(jq -r --arg lane "$1" '(.seats[$lane] // .triage)[]' <<< "$page")
  mapfile -t coordinator < <(jq -r '.coordinator[]' <<< "$page")
  "${command[@]}" "${seat[@]}" "$2" || :
  if [[ "${seat[*]}" != "${coordinator[*]}" ]]; then "${command[@]}" "${coordinator[@]}" "$2" || :; fi
}

# Reads the gap and pages the fixer when it passes the limit; prints the
# reading.
watch_gap() {
  local memory=$1 oldest main reading
  oldest=$(git -C "$watch_tree" log --first-parent --format=%ct refs/watch/main..refs/watch/landing | tail -n 1)
  main=$(git -C "$watch_tree" rev-parse refs/watch/main)
  reading=$(jq -n -c --argjson now "$(date +%s)" --argjson oldest "${oldest:-null}" --arg main "$main" \
    --argjson limit "$watch_limit" --argjson paged "$(jq -c '.paged // null' <<< "$memory")" \
    '{now: $now, oldest: $oldest, main: $main, limit: $limit, paged: $paged}' | jq -c -f "$watch_dir/gap.jq")
  if [[ $(jq -r .page <<< "$reading") == true ]]; then
    watch_page triage "GAP $(jq -r .line <<< "$reading"), past $watch_limit minutes: read #5469 and the newest landing:watch defect"
  fi
  printf '%s\n' "$reading"
}

# Checks out `$1` in the clone, detached, with no change of its own.
watch_checkout() {
  git -C "$watch_tree" checkout --quiet --force --detach "$1"
  git -C "$watch_tree" clean --quiet --force -d
  mise trust --quiet "$watch_tree" > /dev/null 2>&1 || :
}

# Runs the check `$2`, or the whole gate when it is `check`, on commit `$1`
# against the green head, writing its log to `$3`; exits as the check exits.
watch_run() {
  local commit=$1 check=$2 log=$3
  watch_checkout "$commit"
  if [[ $check == check ]]; then
    (cd "$watch_tree" && mise run check) > "$log" 2>&1
  else
    (cd "$watch_tree" \
      && GATE_SCOPE=$(.config/gate-scope/scope.bash 2> /dev/null) \
      && GATE_WITNESS_SCOPE=$(.config/gate-scope/scope.bash --touched 2> /dev/null) \
      && export GATE_SCOPE GATE_WITNESS_SCOPE GATE_TEST_SCOPE=$GATE_WITNESS_SCOPE \
      && mise run "$check") > "$log" 2>&1
  fi
}

# The failing checks a gate's log `$1` names, one per line.
watch_failed() {
  sed -n 's/^\[\(check:[a-z0-9:-]*\)\] ERROR task failed.*/\1/p' "$1" | sort -u
}

# Searches the first parents between the green head `$1` and the red head
# `$2` for the first commit where the check `$3` fails; prints it.
watch_search() {
  local green=$1 head=$2 check=$3 commits results step probe
  commits=$(git -C "$watch_tree" rev-list --first-parent --reverse "$green..$head" | jq -R . | jq -s -c .)
  results='{}'
  while :; do
    step=$(jq -n -c --argjson commits "$commits" --argjson results "$results" '{commits: $commits, results: $results}' \
      | jq -c -f "$watch_dir/search.jq") || return 1
    if probe=$(jq -er '.culprit' <<< "$step"); then
      printf '%s\n' "$probe"
      return 0
    fi
    probe=$(jq -r .probe <<< "$step")
    echo "landing:watch: \`$check\` on ${probe::9}" >&2
    if watch_run "$probe" "$check" "$(mktemp)"; then
      results=$(jq -c --arg c "$probe" '.[$c] = "pass"' <<< "$results")
    else
      results=$(jq -c --arg c "$probe" '.[$c] = "fail"' <<< "$results")
    fi
  done
}

# Gives the red check `$4` of head `$2` an owner: the search names the
# culprit, `owner.jq` the defect and the page; the watcher files the defect
# or comments on the open one, claims it for the lane and pages the lane.
watch_own() {
  local repo=$1 head=$2 green=$3 check=$4 log=$5 culprit pr open lines input owner number observation
  culprit=$(watch_search "$green" "$head" "$check") || { echo "landing:watch: the search for \`$check\` failed" >&2; return 1; }
  pr=$(gh api "repos/$repo/commits/$culprit/pulls" --jq '[.[] | {number, branch: .head.ref, title}] | first // null') || pr=null
  open=$(gh issue list -R "$repo" --state open --label kind:defect --search '"landing:" in:title' --limit 100 --json number,title) || return 1
  lines=$({ grep -F "[$check]" "$log" || :; } | { grep -E 'FAIL|panicked|error|refus' || :; } | awk 'NR <= 30' | jq -R . | jq -s -c .)
  input=$(jq -n -c --arg check "$check" --arg head "$head" --arg green "$green" --arg culprit "$culprit" \
    --argjson pr "$pr" --argjson lines "$lines" --argjson open "$open" \
    '{check: $check, head: $head, green: $green, culprit: $culprit, pr: $pr, lines: $lines, open: $open}')
  owner=$(jq -c -f "$watch_dir/owner.jq" <<< "$input")
  observation=$(mktemp)
  jq -r .observation <<< "$owner" > "$observation"
  number=$(jq -r '.number // empty' <<< "$owner")
  if [[ -z $number ]]; then
    number=$(mise run --quiet issue:file "$(jq -r .title <<< "$owner")" "$observation" kind:defect area:workflow priority:high effort:easy \
      --template landing --fields "$(jq -c '{check: .check, head: .head[0:9], culprit: .culprit[0:9], pr: ((.pr.number // "none") | tostring)}' <<< "$input")" \
      | sed -n 's|.*/issues/\([0-9][0-9]*\)$|\1|p' | tail -n 1)
  else
    gh issue comment "$number" -R "$repo" --body-file "$observation" > /dev/null || :
  fi
  rm -f "$observation"
  [[ -n $number ]] || { echo "landing:watch: the defect for \`$check\` was not filed" >&2; return 1; }
  mise run --quiet claim:take "$number" --lane "$(jq -r .lane <<< "$owner")" || :
  watch_page "$(jq -r .lane <<< "$owner")" "$(jq -r --arg n "$number" '.page | gsub("\\{n\\}"; $n)' <<< "$owner")"
}

# One reading: the gap, then the gate on the newest head when it moved.
# Prints the new state.
watch_once() {
  local repo=$1 memory gap head green log status check
  local -a failed
  memory=$(watch_memory)
  watch_fetch || { echo "landing:watch: the fetch failed; reading again" >&2; printf '%s\n' "$memory"; return 0; }
  gap=$(watch_gap "$memory")
  memory=$(jq -c --argjson gap "$gap" '.gap = $gap | if $gap.page then .paged = $gap.main else . end' <<< "$memory")
  head=$(git -C "$watch_tree" rev-parse refs/watch/landing)
  if [[ $(jq -r '.checked // empty' <<< "$memory") == "$head" ]]; then printf '%s\n' "$memory"; return 0; fi
  # The first green head is `main`'s: the integration cycle passed on it.
  green=$(jq -r '.green // empty' <<< "$memory")
  if [[ -z $green ]] || ! git -C "$watch_tree" merge-base --is-ancestor "$green" "$head" 2> /dev/null; then
    green=$(git -C "$watch_tree" rev-parse refs/watch/main)
  fi
  git -C "$watch_tree" update-ref refs/remotes/origin/landing "$green"
  git -C "$watch_tree" update-ref refs/remotes/origin/main "$(git -C "$watch_tree" rev-parse refs/watch/main)"
  log="${XDG_STATE_HOME:-$HOME/.local/state}/gandr/landing-watch.log"
  SECONDS=0
  watch_run "$head" check "$log" && status=0 || status=$?
  echo "landing:watch: the gate on ${head::9} ran ${SECONDS}s and exited $status" >&2
  if (( status == 0 )); then
    jq -c --arg head "$head" '.green = $head | .checked = $head' <<< "$memory"
    return 0
  fi
  mapfile -t failed < <(watch_failed "$log")
  if (( ${#failed[@]} == 0 )); then
    echo "landing:watch: the gate on ${head::9} failed with no check named (see $log); reading again" >&2
    printf '%s\n' "$memory"
    return 0
  fi
  for check in "${failed[@]}"; do
    watch_own "$repo" "$head" "$green" "$check" "$log" || :
  done
  jq -c --arg head "$head" '.checked = $head' <<< "$memory"
}

# Install (`$1` = install) or remove (`$1` = remove) the service that keeps
# `landing:watch` running from this checkout.
watch_service() {
  service_unit "$1" landing-watch landing:watch 'gandr head watcher of landing (landing:watch)'
}
