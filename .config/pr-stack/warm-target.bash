# Clones the primary worktree's build directory into a new worktree for
# `wt:warm`, without the units of the workspace's members (#7538).
#
# Each member is named `gandr-*`, and each unit of a member reads the
# member's sources or depends on a unit that does. `wt:warm` removes such a
# unit after the copy (#5137), and cargo builds all of them again, so a clone
# of them is work that the removal undoes: on 2026-11-14 they held 111625 of
# the 296285 files of the build directory. A cargo build directory is
# `<profile>/build/<package>/<hash>`. The step clones each entry of the
# build directory whole, but inside each `build/` it clones every package
# except a member's. A `build/` inside a unit is not read, as the walk
# stops at the first one on each path.
#
# One clone command takes all the entries of one directory, and the commands
# of each directory run at once: the clone's time follows its count of files.
# An entry that the worktree holds already is not cloned, so a second run
# overwrites nothing.
#
# warm_target <source> <destination> <clone command...>
#   <clone command> clones its sources, a file or a whole directory, into
#   the directory that its last argument names, keeping links and times.
warm_target() {
  local src=$1 dst=$2 rel status=0 pid
  shift 2
  local -a clone=("$@") pids=()
  local -A builds=() above=()
  [[ -d $src ]] || return 0
  while IFS= read -r -d '' rel; do
    builds[$rel]=1
    while [[ $rel == */* ]]; do
      rel=${rel%/*}
      above[$rel]=1
    done
  done < <(cd "$src" && find . -mindepth 1 -type d -name build -prune -print0)
  warm_level() {
    local dir=$1 entry name rel
    local -a whole=() packages=()
    mkdir -p "$dst/$dir"
    for entry in "$src/$dir"/* "$src/$dir"/.[!.]* "$src/$dir"/..?*; do
      [[ -e $entry || -L $entry ]] || continue
      name=${entry##*/}
      rel=$dir/$name
      if [[ -n ${builds[$rel]:-} ]]; then
        mkdir -p "$dst/$rel"
        packages=()
        for entry in "$src/$rel"/*; do
          [[ ${entry##*/} != gandr-* && ! -e $dst/$rel/${entry##*/} ]] && packages+=("$entry")
        done
        if ((${#packages[@]} > 0)); then
          "${clone[@]}" "${packages[@]}" "$dst/$rel/" &
          pids+=($!)
        fi
      elif [[ -n ${above[$rel]:-} ]]; then
        warm_level "$rel"
      elif [[ ! -e $dst/$rel && ! -L $dst/$rel ]]; then
        whole+=("$entry")
      fi
    done
    if ((${#whole[@]} > 0)); then
      "${clone[@]}" "${whole[@]}" "$dst/$dir/" &
      pids+=($!)
    fi
  }
  warm_level .
  for pid in "${pids[@]}"; do
    wait "$pid" || status=1
  done
  return "$status"
}
