# shellcheck shell=bash
# The judgement of `wt:sweep`: each record of one listing of
# `git worktree list --porcelain` gives one fact line, one kept line or one
# pruned line. The task sources this file, and so does the case harness
# `sweep-gone-cases.bash` (#7490).
#
# The caller declares what the judgement reads: the associative arrays
# `integrated`, `judged`, `first_parent` and `on_remote`; the arrays `facts`,
# `kept`, `pruned` and `asked`, which the judgement fills; and `here`,
# `epoch`, `trunk_ref` and `remote_read`. It sources `sweep.bash` for
# `own_commits` and `held.bash` for `tree_held`, and calls `held_read` first.

# The temporary directories, each as given and as resolved.
tmp_roots=()
for root in "${TMPDIR:-/tmp}" /tmp /var/folders; do
  [[ -d "$root" ]] || continue
  tmp_roots+=("${root%/}/" "$(realpath "$root")/")
done
unset root

# Whether the path `$1` lies under a temporary directory.
under_tmp() {
  local root
  for root in "${tmp_roots[@]}"; do [[ "$1" == "$root"* ]] && return 0; done
  return 1
}

# Judges the worktree of the listing's current record: `path`, `head`,
# `branch`, `flag` and `primary`, which `sweep_judge` sets.
tree() {
  local merged=false moved=false scratch=null holder=null alive=false young=false watched=null commits=null idle=false ahead=null stale=false dirty=null held= gitdir key mark
  [[ -n "$path" ]] || return 0
  if [[ "$flag" == prunable ]]; then pruned+=("pruned $path${branch:+ ($branch)}: its directory is gone"); return 0; fi
  if [[ -n "$flag" ]]; then kept+=("kept $path${branch:+ ($branch)}: $flag"); return 0; fi
  # A listing is a snapshot: the run of another seat can remove a worktree
  # after the listing and before its judgement. Such a worktree is pruned, as
  # one that git lists as prunable is.
  if ! key=$(realpath "$path" 2> /dev/null); then
    pruned+=("pruned $path${branch:+ ($branch)}: its directory went away after the listing")
    return 0
  fi
  if [[ -n "$branch" && -n "${integrated[$key]:-}" && -z "${first_parent[${judged[$key]:-none}]:-}" ]]; then merged=true; fi
  if [[ -n "${judged[$key]:-}" && "$head" != "${judged[$key]}" ]]; then moved=true; fi
  # A branch Worktrunk reads unmerged. The `+` lines of `git cherry` are
  # read by subject. `ahead` counts commits not on the trunk (#5030).
  # Merged pull requests are asked about when the trunk lacks one subject.
  if [[ -n "$branch" && $merged == false && $primary == false && $branch != wip/* ]]; then
    commits=$(own_commits "$trunk_ref" "$head")
    ahead=$(git rev-list --count "$trunk_ref..$head")
    if jq -e 'any(.[]; .on_trunk | not)' <<< "$commits" > /dev/null \
      && $remote_read && [[ -z ${on_remote[$branch]:-} ]] && git config --get "branch.$branch.remote" > /dev/null; then
      asked+=("$branch" "$head")
    fi
  fi
  gitdir=$(sed -n 's/^gitdir: //p' "$path/.git" 2> /dev/null) || gitdir=
  # A live `pr:watch` marks the worktree it runs in (#3798).
  if [[ -n "$gitdir" ]]; then
    for mark in "$gitdir"/gandr-watch-*; do
      if [[ ${mark##*/gandr-watch-} =~ ^[0-9]+$ ]] && kill -0 "${mark##*/gandr-watch-}" 2> /dev/null; then
        watched=${mark##*/gandr-watch-}
        break
      fi
    done
  fi
  if [[ "$path" =~ /gandr-scratch-([0-9]+)\. ]] || { [[ -z "$branch" ]] && under_tmp "$path"; }; then
    if [[ "$path" =~ /gandr-scratch-([0-9]+)\. ]]; then
      holder=${BASH_REMATCH[1]}
      if kill -0 "$holder" 2> /dev/null; then alive=true; fi
    fi
    if [[ -n "$gitdir" && -n $(find "$gitdir" -maxdepth 1 -name index -mmin -240 2> /dev/null) ]]; then young=true; fi
    scratch=$(jq -nc --argjson holder "$holder" --argjson alive "$alive" --argjson young "$young" '{holder: $holder, alive: $alive, young: $young}')
  fi
  # Idle: the tree holds `incremental` caches and no build wrote one within
  # the claim window.
  if [[ -d "$path/target" && -n $(find "$path/target" -mindepth 2 -maxdepth 3 -type d -name incremental -print -quit 2> /dev/null) \
    && -z $(find "$path/target" -mindepth 3 -maxdepth 4 -path '*/incremental/*' -mmin -240 -print -quit 2> /dev/null) ]]; then
    idle=true
  fi
  # Held: a live process works in the tree, read for a tree that is not the
  # primary or the caller's (#6837). The fact is its pid, or `unread` when
  # the process table cannot be read.
  if [[ $primary == false && $key != "$here" ]] && held=$(tree_held "$key"); then held=${held:-unread}; else held=; fi
  # Stale: no commit at the head, no change to the index or `HEAD` in its git
  # directory, and no build under `target/` for 24 hours (#6183). A fresh
  # `wt switch` writes both files, so a tree made and not yet built is not
  # stale. Read only for a tree the sweep may release.
  if [[ $primary == false && $key != "$here" && $watched == null && $scratch == null && -n "$gitdir" && -z $held ]] \
    && (($(git -C "$path" log -1 --format=%ct HEAD 2> /dev/null || echo "$epoch") < epoch - 86400)) \
    && [[ -z $(find "$gitdir" -maxdepth 1 \( -name index -o -name HEAD \) -mmin -1440 -print -quit 2> /dev/null) ]] \
    && [[ ! -d "$path/target" || -z $(find "$path/target" -maxdepth 4 -mmin -1440 -print -quit 2> /dev/null) ]]; then
    stale=true
    if [[ -n $(git -C "$path" status --porcelain 2> /dev/null) ]]; then dirty=true; else dirty=false; fi
    if [[ -z "$branch" ]]; then ahead=$(git rev-list --count "$trunk_ref..$head"); fi
  fi
  facts+=("$(jq -nc --arg path "$path" --arg branch "$branch" --argjson primary "$primary" \
    --argjson cwd "$([[ $key == "$here" ]] && echo true || echo false)" \
    --argjson merged "$merged" --argjson moved "$moved" --argjson scratch "$scratch" --argjson watched "$watched" \
    --slurpfile commits <(printf '%s\n' "$commits") --argjson ahead "$ahead" --argjson idle "$idle" --argjson stale "$stale" --argjson dirty "$dirty" \
    --arg held "$held" \
    '{path: $path, branch: (if $branch == "" then null else $branch end), primary: $primary, cwd: $cwd, merged: $merged, moved: $moved, scratch: $scratch, watched: $watched, held: (if $held == "" then null else $held end), commits: $commits[0], ahead: $ahead, pulls: null, idle: $idle, stale: $stale, dirty: $dirty}')")
}

# Judges each record of the porcelain listing on standard input. An empty line
# ends a record, so the listing ends with one. Git lists the primary worktree
# first.
sweep_judge() {
  local line path= head= branch= flag= primary=true
  while IFS= read -r line; do
    case "$line" in
      "worktree "*) path=${line#worktree } ;;
      "HEAD "*) head=${line#HEAD } ;;
      "branch "*) branch=${line#branch refs/heads/} ;;
      locked*) flag="locked" ;;
      prunable*) flag=prunable ;;
      "")
        tree
        if [[ -n "$path" ]]; then primary=false; fi
        path= head= branch= flag=
        ;;
    esac
  done
}
