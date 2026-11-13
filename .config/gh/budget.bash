# shellcheck shell=bash
# GitHub on a budget: the one `gh` every workflow library sources (stack.bash,
# deps.bash, and through it stall.bash). Every seat on a host polls the same
# pull requests, so a read is answered once a host and shared:
#
# - A read (a GraphQL query, a REST GET, `pr view`, `issue list` and their
#   kin) is cached under `$XDG_CACHE_HOME/gandr/gh` for `GH_BUDGET_TTL`
#   seconds (default 30), keyed by its arguments, the `gh` it runs and the
#   checkout's remote. Concurrent identical reads wait on one lock, so N
#   seats asking at once make one request.
# - Any write on the host makes every cached reading stale, and so does
#   `gh_budget_stale`, which a `git push` site calls.
# - A read or write refused for its rate limit sleeps until the limit resets
#   (the primary limit's reset, read from the free `rate_limit` endpoint) or
#   60 seconds (a secondary limit), recorded for every caller on the host,
#   then runs again. A limit that cannot be read is no back-off: the failure
#   is returned.
#
# Identity is the router's: a read runs as the reviewer, a write as the
# writer. This layer never names an account. `command gh` is the binary on
# PATH, never this function, so nothing here can call itself.

gh_budget_dir=${XDG_CACHE_HOME:-$HOME/.cache}/gandr/gh
gh_budget_ttl=${GH_BUDGET_TTL:-30}

# Whether `gh "$@"` only reads, as the router classifies it: a GraphQL call
# whose query names no mutation, a REST call by GET or with no fields.
gh_budget_reads() {
  local a method='' graphql=0 fields=0 mutation=0
  case ${1:-} in
    api)
      shift
      for a in "$@"; do
        case $a in
          graphql) graphql=1 ;;
          query=@*) if grep -qs mutation "${a#query=@}"; then mutation=1; fi ;;
          *mutation*) mutation=1 ;;
        esac
      done
      if ((graphql)); then ((!mutation)); return; fi
      while (($#)); do
        case $1 in
          -X | --method) method=${2^^}; shift ;;
          -X*) method=${1#-X}; method=${method^^} ;;
          --method=*) method=${1#--method=}; method=${method^^} ;;
          -f | -F | --field | --raw-field | --input) fields=1; shift ;;
          -f* | -F* | --field=* | --raw-field=* | --input=*) fields=1 ;;
        esac
        shift
      done
      [[ $method == GET || (-z $method && $fields == 0) ]]
      ;;
    pr) [[ ${2:-} =~ ^(view|list|checks|diff|status)$ ]] ;;
    issue) [[ ${2:-} =~ ^(view|list|status)$ ]] ;;
    run) [[ ${2:-} =~ ^(view|list)$ ]] ;;
    repo | release | label) [[ ${2:-} =~ ^(view|list)$ ]] ;;
    search) return 0 ;;
    *) return 1 ;;
  esac
}

# The branch whose pull request `gh "$@"` reads, or nothing when the read
# names what it reads (#7143). `pr status` reads the checkout's branch, and so
# do `pr view`, `pr checks` and `pr diff` with no number, URL or branch. A
# detached head gives its commit. So two branches of one host never share
# the answer of such a read, and a read that names its pull request keeps one
# entry for the host.
gh_budget_branch() {
  local a skip=0
  [[ ${1:-} == pr ]] || return 0
  case ${2:-} in
    status) ;;
    view | checks | diff)
      for a in "${@:3}"; do
        if ((skip)); then skip=0; continue; fi
        case $a in
          --json | -q | --jq | -t | --template | -R | --repo | -i | --interval | --color) skip=1 ;;
          -*) ;;
          *) return 0 ;;
        esac
      done
      ;;
    *) return 0 ;;
  esac
  git symbolic-ref -q HEAD 2> /dev/null || git rev-parse -q --verify HEAD 2> /dev/null || :
}

# Seconds since the epoch.
gh_budget_now() { date +%s; }

# Every cached reading on the host made stale.
gh_budget_stale() {
  mkdir -p "$gh_budget_dir" && gh_budget_now > "$gh_budget_dir/written"
}

# Sleep while the host's `$1` (read or write) budget is spent, to its reset
# and up to 30 s past it, so the host's waiting callers do not all wake into
# the same second.
gh_budget_wait() {
  local until now
  [[ -r $gh_budget_dir/limited.$1 ]] || return 0
  until=$(< "$gh_budget_dir/limited.$1")
  now=$(gh_budget_now)
  ((until > now)) || return 0
  echo "gh: the $1 budget is spent; waiting $((until - now)) s, until $(date -d "@$until" +%H:%M 2> /dev/null || date -r "$until" +%H:%M)" >&2
  sleep $((until - now + RANDOM % 30))
}

# The read budget's gauge, read at most once a minute a host from the free
# `rate_limit` endpoint: under a tenth left of the REST or GraphQL hour,
# reads wait for its reset rather than spend the rest.
gh_budget_gauge() {
  local now reset
  now=$(gh_budget_now)
  if [[ -r $gh_budget_dir/gauged ]] && ((now - $(< "$gh_budget_dir/gauged") < 60)); then return 0; fi
  echo "$now" > "$gh_budget_dir/gauged"
  reset=$(command gh api rate_limit --jq '[.resources.core, .resources.graphql] | map(select(.remaining * 10 < .limit) | .reset) | max // 0' 2> /dev/null) || return 0
  [[ $reset =~ ^[0-9]+$ ]] && ((reset > now)) || return 0
  echo "$reset" > "$gh_budget_dir/limited.read"
}

# Record a refusal for its rate limit in `$2` (stderr of a `$1` call), when
# it is one: a read until its limit's reset, or 60 s for a secondary limit
# or a write, whose limit the read identity cannot see. Returns 1 when `$2`
# is no rate limit, or a read's limit cannot be read.
gh_budget_limited() {
  local reset=0 now
  grep -qi 'rate limit' "$2" || return 1
  now=$(gh_budget_now)
  if [[ $1 == read ]]; then
    reset=$(command gh api rate_limit --jq '[.resources.core, .resources.graphql] | map(select(.remaining == 0) | .reset) | max // 0' 2> /dev/null) || return 1
    [[ $reset =~ ^[0-9]+$ ]] || return 1
  fi
  ((reset > now)) || reset=$((now + 60))
  echo "$reset" > "$gh_budget_dir/limited.$1"
}

# `gh "$@"` once, the `$1` budget (read or write) waited on and a rate-limit
# refusal waited out, at most three times. Stdout to `$2`, stderr to `$3`;
# stdin from `$4`, a file read afresh each time, or the caller's when empty.
gh_budget_call() {
  local kind=$1 out=$2 err=$3 in=$4 tries=0 status
  shift 4
  while :; do
    gh_budget_wait "$kind"
    status=0
    if [[ -n $in ]]; then
      command gh "$@" < "$in" > "$out" 2> "$err" || status=$?
    else
      command gh "$@" > "$out" 2> "$err" || status=$?
    fi
    ((status != 0 && tries < 3)) && gh_budget_limited "$kind" "$err" || return "$status"
    tries=$((tries + 1))
  done
}

# Take the lock `$1` (a directory), breaking one whose holder is gone; give
# up after two minutes.
gh_budget_lock() {
  local tries=0 holder
  until mkdir "$1" 2> /dev/null; do
    holder=$(cat "$1/pid" 2> /dev/null) || holder=
    if [[ -n $holder ]] && ! kill -0 "$holder" 2> /dev/null; then rm -rf "$1"; continue; fi
    ((++tries < 1200)) || return 1
    sleep 0.1
  done
  echo "$BASHPID" > "$1/pid"
}

# A read: answered from the host's cache while fresh, else fetched once under
# the reading's lock, with its arguments as the caller wrote them. The key
# holds the branch a read of the checkout's branch answers for.
gh_budget_read() {
  local key entry status=0 fresh_after now
  mkdir -p "$gh_budget_dir"
  key=$(printf '%s\n' "$(type -P gh)" "${GH_REPO:-}" "$(git config --get remote.origin.url 2> /dev/null)" "$(gh_budget_branch "$@")" "$@" | git hash-object --stdin)
  entry=$gh_budget_dir/$key
  gh_budget_wait read
  if ! gh_budget_lock "$entry.lock"; then
    # A holder past two minutes: read uncached, still on the budget.
    gh_budget_call read /dev/stdout /dev/stderr '' "$@"
    return
  fi
  now=$(gh_budget_now)
  fresh_after=$(cat "$gh_budget_dir/written" 2> /dev/null) || fresh_after=0
  if [[ -r $entry.at && -r $entry.out ]] && (($(< "$entry.at") > fresh_after && now - $(< "$entry.at") < gh_budget_ttl)); then
    cat "$entry.out"
    rm -rf "$entry.lock"
    return 0
  fi
  gh_budget_gauge
  gh_budget_wait read
  gh_budget_call read "$entry.out" "$entry.err" '' "$@" || status=$?
  cat "$entry.err" >&2 2> /dev/null
  if ((status == 0)); then echo "$now" > "$entry.at"; else rm -f "$entry.at"; fi
  cat "$entry.out"
  rm -rf "$entry.lock"
  return "$status"
}

gh() {
  if gh_budget_reads "$@"; then
    gh_budget_read "$@"
    return
  fi
  local out err in='' a status=0
  mkdir -p "$gh_budget_dir"
  out=$(mktemp) err=$(mktemp)
  # A write that reads stdin (`--input -`, `--body-file -`) keeps it, so a
  # retry after a rate limit sends it again.
  for a in "$@"; do
    if [[ $a == - || $a == *=@- ]]; then in=$(mktemp); cat > "$in"; break; fi
  done
  gh_budget_call write "$out" "$err" "$in" "$@" || status=$?
  gh_budget_stale
  cat "$out"
  cat "$err" >&2
  rm -f "$out" "$err" ${in:+"$in"}
  return "$status"
}
