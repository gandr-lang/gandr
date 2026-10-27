# The GitHub dependency and sub-issue calls the tracker tasks share (#2902),
# sourced by `unit:check`, `issue:file`, `epic:order`, `epic:deps`,
# `claim:next` and `report:deps`. REST throughout, as `claim:next` reads the
# board: the GraphQL limit, shared by every seat's watches, runs out.
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

# The open issues among those $2 is blocked by, as `#n` words.
deps_open_blockers() {
  deps_blocked_by "$1" "$2" | jq -r '[.[] | select(.state == "open") | "#\(.number)"] | join(", ")'
}

# The sub-issues of $2, as [{number, state}].
deps_sub_issues() {
  gh api --paginate "repos/$1/issues/$2/sub_issues?per_page=100" --jq '[.[] | {number, state}]' | jq -s 'add // []'
}

# Set $2 blocked by $3 unless it is; prints `set #2 blocked by #3` when it
# writes.
deps_block() {
  local repo=$1 issue=$2 blocker=$3
  if deps_blocked_by "$repo" "$issue" | jq -e --argjson n "$blocker" 'any(.[]; .number == $n)' > /dev/null; then
    return 0
  fi
  gh api -X POST "repos/$repo/issues/$issue/dependencies/blocked_by" -F issue_id="$(deps_id "$repo" "$blocker")" > /dev/null
  printf 'set #%s blocked by #%s\n' "$issue" "$blocker"
}

# Make $3 a sub-issue of the epic $2 unless it is, and the epic blocked by it
# while it is open (#2902): the epic's page shows its open work, and an epic
# cannot close over it. An open sub-issue answers an epic's close ruling
# (#2973): its `needs:close-ruling` comes off.
deps_link() {
  local repo=$1 epic=$2 child=$3 parent state
  IFS='|' read -r parent state < <(gh api "repos/$repo/issues/$child" --jq '"\(.parent_issue_url // "" | sub(".*/"; ""))|\(.state)"')
  if [[ $parent != "$epic" ]]; then
    gh api -X POST "repos/$repo/issues/$epic/sub_issues" -F sub_issue_id="$(deps_id "$repo" "$child")" -F replace_parent=true > /dev/null
    printf 'linked #%s under #%s\n' "$child" "$epic"
  fi
  if [[ $state == open ]]; then
    deps_block "$repo" "$epic" "$child"
    if [[ $(gh api "repos/$repo/issues/$epic" --jq '[.labels[].name] | index("needs:close-ruling") != null') == true ]]; then
      gh api -X DELETE "repos/$repo/issues/$epic/labels/needs:close-ruling" > /dev/null
      printf '#%s no longer awaits its close ruling: #%s is open under it\n' "$epic" "$child"
    fi
  fi
}
