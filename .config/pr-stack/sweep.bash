# The facts `wt:sweep` reads from Git for a branch that Worktrunk reads
# unmerged, sourced by the task and by `sweep-subjects.bash`.

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
# `$1`, each `{subject, on_main}`, `on_main` read against `fork_subjects`.
own_commits() {
  local -a listed=()
  mapfile -t listed < <(git cherry "$1" "$2" | awk '/^\+/ { print $2 }')
  if ((${#listed[@]} == 0)); then
    echo '[]'
    return 0
  fi
  git log --no-walk=unsorted --format=%s "${listed[@]}" \
    | jq -R . | jq -sc --argjson main "$(fork_subjects "$1" "$2")" 'map({subject: ., on_main: ($main[.] // false)})'
}
