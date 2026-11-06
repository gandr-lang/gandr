# shellcheck shell=bash
# The one issue a report keeps by its exact title (#5263), sourced by
# `report:deps`, `report:prose`, `report:dead-weight`, `report:gate-time`,
# `ci:cycle` and `ci:known-red`. GitHub's search matches a title's words, so
# a search answers every issue that holds them, and the keeper reads the one
# whose title is exactly the report's. gh names the repository itself:
# `GH_REPO` when it is set, else the checkout's remote, so the repository's
# name costs no read (#5749).

# The issue of exactly the title `$1`, open or closed, as compact JSON
# `{number, state, body}`; `null` when there is none.
issue_found() {
  gh issue list --state all --search "\"$1\" in:title" --json number,title,state,body \
    | jq -c --arg title "$1" '[.[] | select(.title == $title) | {number, state, body}] | first'
}

# Keeps the issue `$2` (as `issue_found` gives it) of the title `$1` in step
# with a report of `$3` findings and the body file `$4`. With findings it
# rewrites the issue, reopening a closed one, or runs the remaining arguments
# to create it when there is none. Without findings it rewrites and closes an
# open issue, and writes nothing otherwise. Prints what it did.
issue_keep() {
  local title=$1 found=$2 count=$3 body=$4 number state
  shift 4
  number=$(jq -r '.number // empty' <<< "$found")
  state=$(jq -r '.state // empty' <<< "$found")
  if (( count == 0 )); then
    if [[ $state == OPEN ]]; then
      gh issue edit "$number" --body-file "$body" > /dev/null
      gh issue close "$number" --reason completed > /dev/null
      echo "closed #$number: no findings"
    else
      echo "$title: no findings"
    fi
  elif [[ -z $number ]]; then
    "$@"
  else
    [[ $state == OPEN ]] || gh issue reopen "$number" > /dev/null
    gh issue edit "$number" --body-file "$body" > /dev/null
    echo "updated #$number: $count finding(s)"
  fi
}
