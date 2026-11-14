# Whether a live process works in a worktree (#6837). A worktree that a
# process holds as its working directory stays: a gate, a watch or a seat's
# shell that loses its directory fails, and the seat loses its run.
# `remove_landed_worktree` (`stack.bash`) and `wt:sweep` read this one
# predicate, so neither removes a worktree in use.
#
# `held_read` reads the process table once, as unique working directories.
# It reads `/proc/<pid>/cwd`, or `lsof -d cwd` on a host with no `/proc`.
# Each process counts, the caller and each of its ancestors among them: the
# shell that runs a landing from its branch's worktree holds that worktree,
# as any other shell does. A host where neither read works leaves
# `held_unread` true.
#
# `tree_held <path>` succeeds when a process works in `<path>` or below it,
# and prints that process's pid. It also succeeds with no pid when the table
# is unread, so a caller keeps the worktree. It fails when no process works
# there.
declare -A held_dirs=()
held_unread=false
held_read() {
  local pid line dir field
  held_dirs=()
  held_unread=false
  # Each read runs from `/`, so the reading process holds no worktree. One
  # `stat` reads every link, `/proc/<pid>/cwd -> <directory>`. A link that
  # it cannot read, as another user's, prints no arrow and stays out.
  if [[ -d /proc/self ]]; then
    while IFS= read -r line; do
      if [[ $line == /proc/*/cwd\ -\>\ * ]]; then
        pid=${line#/proc/}
        pid=${pid%%/cwd -> *}
        dir=${line#*/cwd -> }
        if [[ -z ${held_dirs[$dir]:-} ]]; then held_dirs[$dir]=$pid; fi
      fi
    done < <(cd / && QUOTING_STYLE=literal stat -c '%N' /proc/[0-9]*/cwd 2> /dev/null || true)
  elif command -v lsof > /dev/null; then
    pid=
    while IFS= read -r field; do
      case $field in
        p*) pid=${field#p} ;;
        n*) if [[ -n $pid && -z ${held_dirs[${field#n}]:-} ]]; then held_dirs[${field#n}]=$pid; fi ;;
      esac
    done < <(cd / && lsof -w -a -d cwd -Fpn 2> /dev/null || true)
  else
    held_unread=true
  fi
}
tree_held() {
  local tree=$1 dir
  if [[ $held_unread == true ]]; then return 0; fi
  for dir in "${!held_dirs[@]}"; do
    if [[ $dir == "$tree" || $dir == "$tree"/* ]]; then
      echo "${held_dirs[$dir]}"
      return 0
    fi
  done
  return 1
}
