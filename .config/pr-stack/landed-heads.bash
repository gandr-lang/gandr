# shellcheck shell=bash
# The remote branches the landing watcher deletes (#6185), in two steps so a
# case can move a head between them: `branch_reading` reads each remote head
# and decides it with `landed-heads.jq`, and `branch_delete` deletes the
# decided heads in one push, with a lease on each head as read. Sourced by
# `landing.bash` and by `landed-heads-cases.bash`, after `sweep.bash`, which
# gives `own_commits`.

# The decisions of `landed-heads.jq` for each head of the remote `$1`, read
# against the trunk ref `$2`. `$3` is a file of the branch names that open
# pull requests use, one a line. The arguments after it are the branches that
# outlive every unit. A head whose commits are not here is fetched once. A
# head whose commits still cannot be read stays.
branch_reading() {
  local remote=$1 trunk_ref=$2 used=$3 line name oid commits ahead
  shift 3
  local -a heads=() fetch=()
  mapfile -t heads < <(git ls-remote --heads "$remote" | awk '{ sub("^refs/heads/", "", $2); print $1 "\t" $2 }')
  for line in "${heads[@]}"; do
    git cat-file -e "${line%%$'\t'*}^{commit}" 2> /dev/null || fetch+=("refs/heads/${line#*$'\t'}")
  done
  if ((${#fetch[@]} > 0)); then git fetch --quiet --no-tags "$remote" "${fetch[@]}" 2> /dev/null || true; fi
  for line in "${heads[@]}"; do
    oid=${line%%$'\t'*}
    name=${line#*$'\t'}
    commits=null
    ahead=null
    if git cat-file -e "$oid^{commit}" 2> /dev/null; then
      commits=$(own_commits "$trunk_ref" "$oid")
      ahead=$(git rev-list --count "$trunk_ref..$oid")
    fi
    jq -nc --arg name "$name" --arg oid "$oid" --slurpfile commits <(printf '%s\n' "$commits") --argjson ahead "$ahead" \
      '{name: $name, oid: $oid, commits: $commits[0], ahead: $ahead}'
  done | jq -cs --argjson kept "$(printf '%s\n' "$@" | jq -R . | jq -cs 'map(select(. != ""))')" \
    --slurpfile used <(jq -R . < "$used" | jq -cs 'map(select(. != ""))') \
    '{kept: $kept, used: $used[0], heads: .}' | jq -L "$pr_stack_dir" -c -f "$pr_stack_dir/landed-heads.jq"
}

# Deletes from the remote `$1` each head that the decisions `$2` mark
# `delete`, in one push that is not atomic: a lease holds each head at the
# commit the reading saw, so a head that moved since stays, and the others
# go. Prints the push's line for each head. Returns the push's status.
branch_delete() {
  local remote=$1 decisions=$2 name oid
  local -a leases=() refspecs=()
  while IFS=$'\t' read -r name oid; do
    leases+=("--force-with-lease=refs/heads/$name:$oid")
    refspecs+=(":refs/heads/$name")
  done < <(jq -r '.[] | select(.action == "delete") | [.name, .oid] | @tsv' <<< "$decisions")
  ((${#refspecs[@]} > 0)) || return 0
  git push --porcelain "${leases[@]}" "$remote" "${refspecs[@]}" 2>&1 | awk -F'\t' '/^[-!= *+]\t/ { print $1 " " $2 ": " $3 }'
  return "${PIPESTATUS[0]}"
}
