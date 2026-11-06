# The GitHub dependency and sub-issue calls the tracker tasks share (#2902),
# sourced by `unit:check`, `issue:file`, `epic:order`, `epic:deps`,
# `epics:link`, `claim:next`, `report:deps` and the stall reading
# (`.config/stall/stall.bash`). `issue:file` and `unit:check` read each
# issue they touch in one GraphQL query (`deps_issues`, #5709): a REST read
# takes a request for each list of each issue, and a burst of filings held
# the reader at its cap. The other tasks read one list of one issue through
# REST. `deps_open_graph` reads every open issue in one paginated GraphQL
# pass, at two points a page (#3192).
#
# Each takes the repository first, as `owner/name` or as gh's
# `{owner}/{repo}`. gh fills the placeholders in a path and in a `-F` value
# from `GH_REPO` or the checkout's remote, so a caller reads no name (#5749).
# A setter checks before it writes, so each is idempotent and a rerun repairs
# what a first run missed.

# shellcheck source=../gh/budget.bash
source "${BASH_SOURCE[0]%/*}/../gh/budget.bash"

# The issue's REST id, which the dependency and sub-issue resources take.
deps_id() {
  gh api "repos/$1/issues/$2" --jq .id
}

# The issues $2 is blocked by, as [{number, state}].
deps_blocked_by() {
  gh api --paginate "repos/$1/issues/$2/dependencies/blocked_by?per_page=100" --jq '[.[] | {number, state}]' | jq -s 'add // []'
}

# The issues $2 blocks, as [{number, state}]: an epic $2 belongs to among
# them (#3398).
deps_blocking() {
  gh api --paginate "repos/$1/issues/$2/dependencies/blocking?per_page=100" --jq '[.[] | {number, state}]' | jq -s 'add // []'
}

# The sub-issues of $2, as [{number, state}].
deps_sub_issues() {
  gh api --paginate "repos/$1/issues/$2/sub_issues?per_page=100" --jq '[.[] | {number, state}]' | jq -s 'add // []'
}

# The issues `$3`…, read in one GraphQL query (#5709), as `{"<n>": {number,
# id, state, title, labels, parent, blocked_by, blocking, sub_issues}}`.
# `id` is the REST id that the dependency and sub-issue writes take, and
# `parent` is the parent's number or null. Each list is `[{number, state}]`,
# each state in lower case, as the REST reads give it. `$2` is `body` to read
# each issue's body too, or `-`. A number that names a pull request or no
# issue is left out. A list longer than its page is read again through REST,
# so none comes back short. Up to 25 issues cost one point.
deps_issues() {
  local repo=$1 body= query n reply status=0 list number
  [[ $2 != body ]] || body=body
  shift 2
  query='query($owner: String!, $name: String!) { repository(owner: $owner, name: $name) {'
  for n in $(printf '%s\n' "$@" | sort -nu); do
    [[ $n =~ ^[1-9][0-9]*$ ]] && query+=" i$n: issueOrPullRequest(number: $n) { ...deps }"
  done
  [[ $query == *'...deps'* ]] || { echo '{}'; return 0; }
  query+=" } } fragment deps on IssueOrPullRequest { ... on Issue { number state fullDatabaseId title $body labels(first: 100) { nodes { name } } parent { number }"
  query+=' blockedBy(first: 100) { totalCount nodes { number state } } blocking(first: 100) { totalCount nodes { number state } } subIssues(first: 100) { totalCount nodes { number state } } } }'
  # A number that names nothing is a NOT_FOUND error beside the data, and gh
  # then prints the whole reply and exits 1. Any other error refuses the read.
  reply=$(gh api graphql -F owner="${repo%/*}" -F name="${repo#*/}" -f query="$query") || status=$?
  if ! jq -e '.data.repository != null and all(.errors[]?; .type == "NOT_FOUND")' <<< "$reply" > /dev/null 2>&1; then
    echo "deps_issues: the read of #$* failed (exit $status)" >&2
    return 1
  fi
  reply=$(jq -c 'def listed: [.nodes[] | {number, state: (.state | ascii_downcase)}];
    [.data.repository[] | select(. != null and .number != null)]
    | map({key: "\(.number)", value: ({number, id: (.fullDatabaseId | tonumber), state: (.state | ascii_downcase), title,
        labels: [.labels.nodes[].name], parent: .parent.number,
        blocked_by: (.blockedBy | listed), blocked_by_total: .blockedBy.totalCount,
        blocking: (.blocking | listed), blocking_total: .blocking.totalCount,
        sub_issues: (.subIssues | listed), sub_issues_total: .subIssues.totalCount}
        + (if has("body") then {body: (.body // "")} else {} end))})
    | from_entries' <<< "$reply")
  for list in blocked_by:deps_blocked_by blocking:deps_blocking sub_issues:deps_sub_issues; do
    for number in $(jq -r --arg list "${list%%:*}" 'to_entries[] | select((.value[$list] | length) < .value["\($list)_total"]) | .key' <<< "$reply"); do
      reply=$(jq -c --arg list "${list%%:*}" --arg n "$number" --argjson read "$("${list#*:}" "$repo" "$number")" '.[$n][$list] = $read' <<< "$reply")
    done
  done
  jq -c 'map_values(del(.blocked_by_total, .blocking_total, .sub_issues_total))' <<< "$reply"
}

# Every open issue's dependencies and sub-issues in one paginated GraphQL
# pass (#3192), as `{"<n>": {blocked_by: [{number, state}], sub_issues:
# [{number, state}]}}`, each state in lower case as the REST reads give it.
# A list longer than the page the pass asks for is read again through REST,
# so none comes back short.
deps_open_graph() {
  local repo=$1 graph number
  graph=$(gh api graphql --paginate -F owner="${repo%/*}" -F name="${repo#*/}" -f query='
    query($owner: String!, $name: String!, $endCursor: String) {
      repository(owner: $owner, name: $name) {
        issues(states: OPEN, first: 100, after: $endCursor) {
          pageInfo { hasNextPage endCursor }
          nodes {
            number
            blockedBy(first: 100) { totalCount nodes { number state } }
            subIssues(first: 100) { totalCount nodes { number state } }
          }
        }
      }
    }' --jq '.data.repository.issues.nodes[]' \
    | jq -s 'map({key: "\(.number)", value: {
        blocked_by: [.blockedBy.nodes[] | {number, state: (.state | ascii_downcase)}], blocked_total: .blockedBy.totalCount,
        sub_issues: [.subIssues.nodes[] | {number, state: (.state | ascii_downcase)}], sub_total: .subIssues.totalCount}}) | from_entries')
  for number in $(jq -r 'to_entries[] | select((.value.blocked_by | length) < .value.blocked_total) | .key' <<< "$graph"); do
    graph=$(jq --arg n "$number" --argjson read "$(deps_blocked_by "$repo" "$number")" '.[$n].blocked_by = $read' <<< "$graph")
  done
  for number in $(jq -r 'to_entries[] | select((.value.sub_issues | length) < .value.sub_total) | .key' <<< "$graph"); do
    graph=$(jq --arg n "$number" --argjson read "$(deps_sub_issues "$repo" "$number")" '.[$n].sub_issues = $read' <<< "$graph")
  done
  jq -c 'map_values({blocked_by, sub_issues})' <<< "$graph"
}

# Set $2 blocked by $3 unless it is; prints `set #2 blocked by #3` when it
# writes.
deps_block() {
  local repo=$1 issue=$2 blocker=$3
  if deps_blocked_by "$repo" "$issue" | jq -e --argjson n "$blocker" 'any(.[]; .number == $n)' > /dev/null; then
    return 0
  fi
  deps_set_block "$repo" "$issue" "$blocker"
}

# Set $2 blocked by $3, which a read has found it is not; prints `set #2
# blocked by #3`. `$4` is the REST id of $3 when a reading holds it, and it
# is read otherwise.
deps_set_block() {
  gh api -X POST "repos/$1/issues/$2/dependencies/blocked_by" -F issue_id="${4:-$(deps_id "$1" "$3")}" > /dev/null || return
  printf 'set #%s blocked by #%s\n' "$2" "$3"
}

# Make $3 a sub-issue of the epic $2 unless it is, and the epic blocked by it
# (#2902, #3398): the epic's page shows its work, and the epic closes once
# every issue it is blocked by and every sub-issue it holds is closed.
deps_link() {
  local repo=$1 epic=$2 child=$3 parent
  parent=$(gh api "repos/$repo/issues/$child" --jq '.parent_issue_url // "" | sub(".*/"; "")')
  if [[ $parent != "$epic" ]]; then
    gh api -X POST "repos/$repo/issues/$epic/sub_issues" -F sub_issue_id="$(deps_id "$repo" "$child")" -F replace_parent=true > /dev/null
    printf 'linked #%s under #%s\n' "$child" "$epic"
  fi
  deps_block "$repo" "$epic" "$child"
}

# Make $3, an issue filed in this run, a sub-issue of the epic $2, and the
# epic blocked by it (#5709). A new issue has no parent and blocks nothing,
# so nothing is read first. `$4` is its REST id.
deps_link_filed() {
  gh api -X POST "repos/$1/issues/$2/sub_issues" -F sub_issue_id="$4" > /dev/null
  printf 'linked #%s under #%s\n' "$3" "$2"
  deps_set_block "$1" "$2" "$3" "$4"
}
