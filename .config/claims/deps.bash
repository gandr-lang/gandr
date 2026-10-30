# The GitHub dependency and sub-issue calls the tracker tasks share (#2902),
# sourced by `unit:check`, `issue:file`, `epic:order`, `epic:deps`,
# `epics:link`, `claim:next`, `report:deps` and the stall reading
# (`.config/stall/stall.bash`). REST for the per-issue
# reads, as `claim:next` reads the board: the GraphQL limit, shared by every
# seat's watches, runs out. The one exception is `deps_open_graph`, a single pass
# over every open issue at two points a page, where REST takes a call per
# issue (#3192).
#
# Each takes the repository as `owner/name` first. A setter checks before it
# writes, so each is idempotent and a rerun repairs what a first run missed.

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

# The open `kind:epic` issues the body $2 names as its epic (`epic_refs` in
# `sections.jq`: an `Advances`, `Part of` or `from:` line), one number a line.
deps_named_epics() {
  local repo=$1 body=$2 n
  for n in $(jq -R -s -r -L "$(dirname "${BASH_SOURCE[0]}")" 'include "sections"; epic_refs[]' <<< "$body"); do
    gh api "repos/$repo/issues/$n" \
      --jq 'select(.state == "open" and .pull_request == null and ([.labels[].name] | index("kind:epic") != null)) | .number' 2> /dev/null || true
  done
}

# Set each open epic the body $3 names (`deps_named_epics`) blocked by $2
# unless it is (#3398): an epic is blocked by its units, and closes once
# every one is closed.
deps_block_named_epics() {
  local repo=$1 issue=$2 body=$3 epic
  for epic in $(deps_named_epics "$repo" "$body"); do
    [[ $epic != "$issue" ]] || continue
    deps_block "$repo" "$epic" "$issue"
  done
}

# The sub-issues of $2, as [{number, state}].
deps_sub_issues() {
  gh api --paginate "repos/$1/issues/$2/sub_issues?per_page=100" --jq '[.[] | {number, state}]' | jq -s 'add // []'
}

# The programme focus (#3959): `.config/issues/focus.toml`'s epics and every
# sub-issue under them in any state, a sub-epic's in turn, as `{epics,
# members: [{number, epic, parent, state, labels}]}`, `epic` the focus epic a
# member falls under and the members of one parent in its sub-issue order.
# Prints `null` when the file names no epic.
deps_focus() {
  local repo=$1 focused epic parent children members='[]'
  local -a pending nested
  focused=$(yq -p toml -o json '.epics // []' "$(dirname "${BASH_SOURCE[0]}")/../issues/focus.toml" | jq -c .) || return 1
  if [[ $focused == '[]' ]]; then
    echo null
    return
  fi
  for epic in $(jq -r '.[]' <<< "$focused"); do
    pending=("$epic")
    while ((${#pending[@]} > 0)); do
      parent=${pending[0]}
      pending=("${pending[@]:1}")
      children=$(gh api --paginate "repos/$repo/issues/$parent/sub_issues?per_page=100" \
        --jq '[.[] | {number, state, labels: [.labels[].name]}]' | jq -s -c 'add // []') || return 1
      members=$(jq -c --argjson epic "$epic" --argjson parent "$parent" --argjson children "$children" \
        '. + [$children[] | . + {epic: $epic, parent: $parent}]' <<< "$members")
      mapfile -t nested < <(jq -r '.[] | select(.labels | index("kind:epic")) | .number' <<< "$children")
      pending+=("${nested[@]}")
    done
  done
  jq -n -c --argjson epics "$focused" --argjson members "$members" '{$epics, $members}'
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
# blocked by #3`.
deps_set_block() {
  gh api -X POST "repos/$1/issues/$2/dependencies/blocked_by" -F issue_id="$(deps_id "$1" "$3")" > /dev/null || return
  printf 'set #%s blocked by #%s\n' "$2" "$3"
}

# Make $3 a sub-issue of the epic $2 unless it is, and the epic blocked by it
# (#2902, #3398): the epic's page shows its work, and the epic closes once
# every issue it is blocked by is closed.
deps_link() {
  local repo=$1 epic=$2 child=$3 parent
  parent=$(gh api "repos/$repo/issues/$child" --jq '.parent_issue_url // "" | sub(".*/"; "")')
  if [[ $parent != "$epic" ]]; then
    gh api -X POST "repos/$repo/issues/$epic/sub_issues" -F sub_issue_id="$(deps_id "$repo" "$child")" -F replace_parent=true > /dev/null
    printf 'linked #%s under #%s\n' "$child" "$epic"
  fi
  deps_block "$repo" "$epic" "$child"
}
