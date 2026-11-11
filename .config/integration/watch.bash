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
# directory, whose objects link those of this checkout's repository. So
# the gate holds the lock of the lane `watch` and one of the host's gate
# slots (`.config/mise/gate.bash`), never a seat's lane. The clone reads
# `landing` and `main` into `refs/watch/`. Its `origin/landing` holds the
# last green head, so the gate reads the move since that head as its
# change, as `pr:open` reads a branch's change against its fork. A move of
# `landing` during a run waits for the run to end, and the next run checks
# the newest head alone. A red check runs on the green head first: a check
# that fails there fails for the host, and the watcher pages the fixer and
# files nothing.
#
# The watcher calls GitHub only for a red head: one read of the culprit's
# pull request, one read of the open `landing:` defects, and the writes of
# one defect, its claim and its page. A green head and an unmoved one call
# nothing.
#
# The state is `watch_state`: `green`, the last head where the gate passes;
# `checked`, the last head the gate ran on; `gap`, the last reading of the
# gap; and `paged`, the head of `main` at the last page of the gap.
#
# The service runs from a checkout of its own, `watch_home` under the state
# directory (#6653). No sweep of a lane's worktrees removes it, since it is a
# clone and no worktree. Before each reading the service sets it to
# `origin/landing`, and the reading sources `watch.bash` from it in a fresh
# shell. So the service runs landing's own watcher, with no restart. The
# gate's clone, `watch_tree`, holds a head under test, which can be red, so
# the service never runs its own code from there.

watch_dir="$(git rev-parse --show-toplevel)/.config/integration"
watch_state="${XDG_STATE_HOME:-$HOME/.local/state}/gandr/landing-watch.json"
watch_tree="${XDG_STATE_HOME:-$HOME/.local/state}/gandr/watch-landing"
watch_home="${XDG_STATE_HOME:-$HOME/.local/state}/gandr/watch-service"
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

# Makes the service's checkout when it is absent, then sets it to
# `origin/landing` (#6653). A local clone links the objects of this
# checkout's repository, so it copies no object, and it keeps them when a
# sweep removes that checkout. Its `origin` is the remote of this checkout.
watch_home_sync() {
  if [[ ! -d "$watch_home/.git" ]]; then
    mkdir -p "$(dirname "$watch_home")"
    git clone --quiet --no-checkout "$(git rev-parse --path-format=absolute --git-common-dir)" "$watch_home" || return 1
    git -C "$watch_home" remote set-url origin "$(git remote get-url origin)" || return 1
  fi
  git -C "$watch_home" fetch --quiet origin '+refs/heads/landing:refs/remotes/origin/landing' || return 1
  git -C "$watch_home" checkout --quiet --force --detach refs/remotes/origin/landing || return 1
  git -C "$watch_home" clean --quiet --force -d
  mise trust --quiet "$watch_home" > /dev/null 2>&1 || :
}

# One reading of the repository `$1` in a fresh shell (#6653). The shell
# sources this script from the checkout again, so a change to the checkout
# takes effect at the next reading, with no restart of the service. The
# shell keeps the options that a command substitution of the loop holds.
watch_reading() {
  bash -c 'set -uo pipefail; source "$1/watch.bash" && watch_once "$2"' _ "$watch_dir" "$1"
}

# A seat's gate runs with `GH_TOKEN` set (#6644). With none, a host's wrapper
# of gh asks the next gh on `PATH` for a token, and in a case over a gh stub
# that is the stub, which refuses. So the watcher's gate runs with the token
# that `gh auth token` gives. A token already set stays, and a failed read
# leaves it unset, as before.
watch_token() {
  local token
  if [[ -z ${GH_TOKEN:-} ]] && token=$(gh auth token 2> /dev/null) && [[ -n $token ]]; then
    export GH_TOKEN=$token
  fi
}

# Makes the clone when it is absent, then reads `landing`, `main` and
# `integration` into its `refs/watch/`. A local clone links the objects of
# this checkout's repository, so it copies no object. A clone of a shallow
# repository is shallow too, and a check that clones the clone again then
# reads it through a pack of its refs alone: a commit that the check wrote
# is not in that pack (#6587). So the first fetch deepens the clone to the
# whole history, and each later one keeps it whole.
watch_fetch() {
  local -a deepen=()
  if [[ ! -d "$watch_tree/.git" ]]; then
    mkdir -p "$(dirname "$watch_tree")"
    git clone --quiet --no-checkout "$(git rev-parse --path-format=absolute --git-common-dir)" "$watch_tree"
    git -C "$watch_tree" remote set-url origin "$(git remote get-url origin)"
  fi
  if [[ $(git -C "$watch_tree" rev-parse --is-shallow-repository) == true ]]; then deepen=(--unshallow); fi
  git -C "$watch_tree" fetch --quiet "${deepen[@]}" origin '+refs/heads/landing:refs/watch/landing' \
    '+refs/heads/main:refs/watch/main' '+refs/heads/integration:refs/watch/integration'
}

# Pages the seat of lane `$1` with the line `$2`, the triage seat for a
# lane with no seat, through the page script of the stall detector's
# configuration. With `$3` = `coordinator`, it pages the coordinator with
# the same line too.
watch_page() {
  local page
  local -a command seat coordinator
  page=$(stall_configuration | jq -c '.page // empty')
  [[ -n $page ]] || { echo "landing:watch: no page configuration; the line is: $2" >&2; return 1; }
  mapfile -t command < <(jq -r '.command[]' <<< "$page")
  mapfile -t seat < <(jq -r --arg lane "$1" '(.seats[$lane] // .triage)[]' <<< "$page")
  mapfile -t coordinator < <(jq -r '.coordinator[]' <<< "$page")
  "${command[@]}" "${seat[@]}" "$2" || :
  if [[ ${3:-} == coordinator && "${seat[*]}" != "${coordinator[*]}" ]]; then "${command[@]}" "${coordinator[@]}" "$2" || :; fi
}

# Reads the gap and pages the fixer when `gap.jq` says so, and the
# coordinator too when no cycle runs; prints the reading.
watch_gap() {
  local memory=$1 oldest main integration reading
  oldest=$(git -C "$watch_tree" log --first-parent --format=%ct refs/watch/main..refs/watch/landing | tail -n 1)
  main=$(git -C "$watch_tree" rev-parse refs/watch/main)
  integration=$(git -C "$watch_tree" rev-parse refs/watch/integration)
  reading=$(jq -n -c --argjson now "$(date +%s)" --argjson oldest "${oldest:-null}" --arg main "$main" \
    --arg integration "$integration" --argjson limit "$watch_limit" --argjson paged "$(jq -c '.paged // null' <<< "$memory")" \
    '{now: $now, oldest: $oldest, main: $main, integration: $integration, limit: $limit, paged: $paged}' | jq -c -f "$watch_dir/gap.jq")
  if [[ $(jq -r .page <<< "$reading") == true ]]; then
    watch_page triage "GAP $(jq -r .line <<< "$reading"), past $watch_limit minutes: read #5469 and the newest landing:watch defect" \
      "$(jq -r 'if .coordinator then "coordinator" else "" end' <<< "$reading")"
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
# The run is a background gate (#6638): at niceness 19 and in no host slot,
# so a lane's gate beside it loses neither CPU nor a slot to it.
watch_run() {
  local commit=$1 check=$2 log=$3
  watch_checkout "$commit"
  if [[ $check == check ]]; then
    (cd "$watch_tree" && GANDR_GATE_BACKGROUND=1 nice -n 19 mise run check) > "$log" 2>&1
  else
    (cd "$watch_tree" \
      && GATE_SCOPE=$(.config/gate-scope/scope.bash 2> /dev/null) \
      && GATE_WITNESS_SCOPE=$(.config/gate-scope/scope.bash --touched 2> /dev/null) \
      && export GATE_SCOPE GATE_WITNESS_SCOPE GATE_TEST_SCOPE=$GATE_WITNESS_SCOPE \
      && GANDR_GATE_BACKGROUND=1 nice -n 19 mise run "$check") > "$log" 2>&1
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

# Whether a newer head of `landing` repairs the red check `$2` of head `$1`
# (#6679). The watcher fetches, and when `landing` stands past `$1`, it runs
# the check on the newest head. A pass there prints that head and exits 0,
# and the search does not run: its culprit names a red that `landing` no
# longer holds. A red check there, an unmoved head or a failed fetch exits 1,
# and the search runs as before.
watch_repaired() {
  local head=$1 check=$2 newest log status=0
  watch_fetch || return 1
  newest=$(git -C "$watch_tree" rev-parse refs/watch/landing) || return 1
  [[ $newest != "$head" ]] || return 1
  git -C "$watch_tree" merge-base --is-ancestor "$head" "$newest" || return 1
  log=$(mktemp)
  watch_run "$newest" "$check" "$log" || status=$?
  rm -f "$log"
  (( status == 0 )) || return 1
  printf '%s\n' "$newest"
}

# Gives the red check `$4` of head `$2` an owner: the search names the
# culprit, `owner.jq` the defect and the page; the watcher files the defect
# or comments on the open one, claims it for the lane and pages the lane.
watch_own() {
  local repo=$1 head=$2 green=$3 check=$4 log=$5 culprit pr open input owner number observation
  # A check that fails on the green head too fails for the host, not for
  # the move: the watcher pages the fixer and files nothing.
  if ! watch_run "$green" "$check" "$(mktemp)"; then
    watch_page triage "LANDING \`$check\` fails on the green head ${green::9} too, so the watcher files nothing: read $log"
    return 1
  fi
  culprit=$(watch_search "$green" "$head" "$check") || { echo "landing:watch: the search for \`$check\` failed" >&2; return 1; }
  pr=$(gh api "repos/$repo/commits/$culprit/pulls" --jq '[.[] | {number, branch: .head.ref, title}] | first // null') || pr=null
  open=$(gh issue list -R "$repo" --state open --label kind:defect --search '"landing:" in:title' --limit 100 --json number,title) || return 1
  # The defect holds the check's own last lines, by its prefix alone (#6659,
  # `lines.jq`). The log reaches jq on standard input, never as one argument.
  input=$(jq -R . "$log" | jq -s -c --arg check "$check" --arg head "$head" --arg green "$green" --arg culprit "$culprit" \
    --argjson pr "$pr" --argjson open "$open" \
    '{check: $check, head: $head, green: $green, culprit: $culprit, pr: $pr, log: ., open: $open}')
  owner=$(jq -c -L "$watch_dir" -f "$watch_dir/owner.jq" <<< "$input")
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
  local repo=$1 memory gap head green log status check newest
  local -a failed
  memory=$(watch_memory)
  watch_fetch || { echo "landing:watch: the fetch failed; reading again" >&2; printf '%s\n' "$memory"; return 0; }
  gap=$(watch_gap "$memory")
  memory=$(jq -c --argjson gap "$gap" '.gap = ($gap | del(.paged)) | if $gap.page then .paged = $gap.paged else . end' <<< "$memory")
  head=$(git -C "$watch_tree" rev-parse refs/watch/landing)
  if [[ $(jq -r '.checked // empty' <<< "$memory") == "$head" ]]; then printf '%s\n' "$memory"; return 0; fi
  # The state holds the gap before the gate runs (#6675): a gate and the
  # search of a red head can run an hour, and the report reads the gap
  # meanwhile. The loop writes the state again when the reading returns.
  watch_remember "$(jq -c --argjson read "$(date +%s)" '.read = $read' <<< "$memory")"
  # The first green head is `main`'s: the integration cycle passed on it.
  green=$(jq -r '.green // empty' <<< "$memory")
  if [[ -z $green ]] || ! git -C "$watch_tree" merge-base --is-ancestor "$green" "$head" 2> /dev/null; then
    green=$(git -C "$watch_tree" rev-parse refs/watch/main)
  fi
  git -C "$watch_tree" update-ref refs/remotes/origin/landing "$green"
  git -C "$watch_tree" update-ref refs/remotes/origin/main "$(git -C "$watch_tree" rev-parse refs/watch/main)"
  log="${XDG_STATE_HOME:-$HOME/.local/state}/gandr/landing-watch.log"
  watch_token
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
    if newest=$(watch_repaired "$head" "$check"); then
      echo "landing:watch: \`$check\` red on ${head::9} is green on ${newest::9}; no search" >&2
      continue
    fi
    watch_own "$repo" "$head" "$green" "$check" "$log" || :
  done
  jq -c --arg head "$head" '.checked = $head' <<< "$memory"
}

# Install (`$1` = install) or remove (`$1` = remove) the service that keeps
# `landing:watch` running, in the background (#6638). An install sets the
# service's checkout to `origin/landing` first, and the service runs from
# there (#6653).
watch_service() {
  if [[ $1 == install ]]; then
    watch_home_sync || { echo "landing:watch --install: $watch_home cannot take origin/landing" >&2; return 1; }
  fi
  (cd "$watch_home" 2> /dev/null || :; service_unit "$1" landing-watch landing:watch 'gandr head watcher of landing (landing:watch)' background)
}
