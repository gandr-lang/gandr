# shellcheck shell=bash
# The one issue a report keeps by its exact title (#5263), sourced by
# `report:deps`, `report:prose` and `report:gate-time`. GitHub's search
# matches a title's words, so a search answers every issue that holds them,
# and the keeper reads the one whose title is exactly the report's.

# The issue of exactly the title `$2` in the repository `$1`, open or closed,
# as compact JSON `{number, state, body}`; `null` when there is none.
issue_found() {
  gh issue list --repo "$1" --state all --search "\"$2\" in:title" --json number,title,state,body \
    | jq -c --arg title "$2" '[.[] | select(.title == $title) | {number, state, body}] | first'
}

# Keeps the issue `$3` (as `issue_found` gives it) of the title `$2` in the
# repository `$1` in step with a report of `$4` findings and the body file
# `$5`. With findings it rewrites the issue, reopening a closed one, or runs
# the remaining arguments to create it when there is none. Without findings
# it rewrites and closes an open issue, and writes nothing otherwise. Prints
# what it did.
issue_keep() {
  local repo=$1 title=$2 found=$3 count=$4 body=$5 number state
  shift 5
  number=$(jq -r '.number // empty' <<< "$found")
  state=$(jq -r '.state // empty' <<< "$found")
  if (( count == 0 )); then
    if [[ $state == OPEN ]]; then
      gh issue edit "$number" --repo "$repo" --body-file "$body" > /dev/null
      gh issue close "$number" --repo "$repo" --reason completed > /dev/null
      echo "closed #$number: no findings"
    else
      echo "$title: no findings"
    fi
  elif [[ -z $number ]]; then
    "$@"
  else
    [[ $state == OPEN ]] || gh issue reopen "$number" --repo "$repo" > /dev/null
    gh issue edit "$number" --repo "$repo" --body-file "$body" > /dev/null
    echo "updated #$number: $count finding(s)"
  fi
}
