# The facts `wt:sweep` reads for a branch that Worktrunk reads unmerged: its
# commits from Git, and its merged pull requests from GitHub. Sourced by the
# task, by `sweep-subjects.bash` and by `sweep-pulls.bash`.

# The subjects of the commits that the trunk `$1` gains after the head `$2`
# forks from it, a queue merge's ` (#n)` dropped, as one JSON object of
# `subject: true`. The queue lands a branch after its fork, so a commit the
# trunk holds before the fork never lands that branch: a subject that only
# repeats an older one is no landing (#4227, #5118).
fork_subjects() {
  local base
  base=$(git merge-base "$1" "$2") || { echo '{}'; return 0; }
  git log --format=%s "$base..$1" | sed -E 's/ \(#[0-9]+\)$//' \
    | jq -R . | jq -sc 'map({key: ., value: true}) | from_entries'
}

# The `+` commits that `git cherry` lists for the head `$2` against the trunk
# `$1`, each `{subject, on_trunk}`, `on_trunk` read against `fork_subjects`.
own_commits() {
  local -a listed=()
  mapfile -t listed < <(git cherry "$1" "$2" | awk '/^\+/ { print $2 }')
  if ((${#listed[@]} == 0)); then
    echo '[]'
    return 0
  fi
  git log --no-walk=unsorted --format=%s "${listed[@]}" \
    | jq -R . | jq -sc --slurpfile trunk <(fork_subjects "$1" "$2") 'map({subject: ., on_trunk: ($trunk[0][.] // false)})'
}

# The merged pull requests of each branch that `wt:sweep` asks about (#5839),
# as one JSON object `{"<branch>": [{number, subjects}]}`. A branch whose read
# failed is `null`. After the record directory `$1`, the arguments go in
# pairs, `<branch> <head>`. The answer for a branch at its head is kept in
# `$1/<head>/<branch>.json`, with `%` and `/` of the name encoded. So no sweep
# of the clone asks about that branch at that head again. A record does not go
# stale: the sweep asks only about a branch whose remote branch is gone, and a
# pull request whose head branch is gone merges no more. The branches with no
# record are read in one GraphQL query, with one alias for each branch and
# 100 aliases a query. Each name goes in as a `-f` variable, so gh never reads
# a branch name as a number. The query asks for the headlines alone, 1 point
# for 9 branches: `gh pr list --json commits` asks for each commit's authors
# too, 29 points a call (#5061). A failed query writes no record.
merged_pulls() {
  local dir=$1 branch file reply json tmp vars fields n i
  local -a asked=() names=() heads=() args=()
  local -A answer=()
  shift
  while (( $# >= 2 )); do
    branch=$1
    file=${branch//%/%25}
    file=$dir/$2/${file//\//%2F}.json
    asked+=("$branch")
    if [[ -f $file ]]; then
      answer[$branch]=$(< "$file")
    else
      names+=("$branch")
      heads+=("$2")
    fi
    shift 2
  done
  for (( i = 0; i < ${#names[@]}; i += 100 )); do
    args=(-F owner='{owner}' -F name='{repo}')
    vars='$owner: String!, $name: String!'
    fields=
    for (( n = i; n < i + 100 && n < ${#names[@]}; n++ )); do
      args+=(-f "h$n=${names[n]}")
      vars+=", \$h$n: String!"
      fields+=" b$n: pullRequests(headRefName: \$h$n, states: MERGED, first: 10) { nodes { number commits(first: 100) { nodes { commit { messageHeadline } } } } }"
    done
    reply=$(gh api graphql "${args[@]}" -f query="query($vars) { repository(owner: \$owner, name: \$name) {$fields } }" \
      --jq '.data.repository | to_entries[] | "\(.key | ltrimstr("b"))\t\(.value.nodes | map({number, subjects: [.commits.nodes[].commit.messageHeadline]}) | tojson)"' 2> /dev/null) || continue
    while IFS=$'\t' read -r n json; do
      [[ -n $n ]] || continue
      branch=${names[n]}
      file=${branch//%/%25}
      file=$dir/${heads[n]}/${file//\//%2F}.json
      mkdir -p "${file%/*}"
      tmp=$(mktemp "$file.XXXXXX") && printf '%s\n' "$json" > "$tmp" && mv -f "$tmp" "$file"
      answer[$branch]=$json
    done <<< "$reply"
  done
  for branch in "${asked[@]}"; do printf '%s\t%s\n' "$branch" "${answer[$branch]:-null}"; done \
    | jq -Rn '[inputs | split("\t") | {key: .[0], value: (.[1] | fromjson)}] | from_entries'
}

# The fact lines of `wt:sweep` on stdin, one JSON object a line, with the
# answers `$1` of `merged_pulls` in `pulls` of each branch it answers. Every
# other line passes through as it is.
pulls_into_facts() {
  jq -c --argjson answers "$1" '.branch as $branch | if $branch != null and ($answers | has($branch)) then .pulls = $answers[$branch] else . end'
}
