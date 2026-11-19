# The kept-tree rule (#6837, #7533). A worktree stays for one of two reasons.
# A live process holds it as its working directory: a gate, a watch or a
# seat's shell that loses its directory fails, and the seat loses its run. Or
# the caller cannot delete its files, as the files of another user that a
# container's job leaves under `target/`. `remove_landed_worktree`
# (`stack.bash`) and `wt:sweep` read this one rule. Each names a kept tree in
# one line and goes on, so one tree never stops a run.
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
#
# `tree_delete <label> <step> <path>...` deletes each path. When a file stays
# that the caller cannot delete, it prints `kept <label>: <step> cannot delete
# <file>`, with the deepest file left, and fails. The caller keeps the tree
# and goes on to the next.
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
tree_delete() {
  local label=$1 step=$2 left
  shift 2
  rm -rf "$@" 2> /dev/null && return 0
  left=$(find "$@" -depth -print -quit 2> /dev/null) || true
  echo "kept $label: $step cannot delete ${left:-$1}"
  return 1
}
