#!/usr/bin/env bash
# The cases of `held.bash` (#6837), over live processes. A process that runs
# in a scratch tree, or below it, holds that tree, and `tree_held` names its
# pid. A tree that no process works in is free. The caller works in a third
# tree, which it holds. A shell that moves to `/` before it reads, as a
# landing moves to the primary worktree, leaves its parent in that tree, and
# the parent holds it.
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
source "$here/held.bash"
scratch=$(realpath "$(mktemp -d)")
holder=
cleanup() {
  [[ -z $holder ]] || kill "$holder" 2> /dev/null || true
  cd /
  rm -rf "$scratch"
}
trap cleanup EXIT
mkdir -p "$scratch/held/below" "$scratch/free" "$scratch/caller"
(cd "$scratch/held/below" && exec sleep 300) &
holder=$!
# The process enters its directory before the read: wait until it does.
for _ in $(seq 50); do
  [[ $(readlink "/proc/$holder/cwd" 2> /dev/null || lsof -w -a -p "$holder" -d cwd -Fn 2> /dev/null | sed -n 's/^n//p') == "$scratch/held/below" ]] && break
  sleep 0.1
done
cd "$scratch/caller"
held_read
failed=0
fail() {
  printf 'held case FAILED: %s\n  wanted: %s\n  got:    %s\n' "$1" "$2" "$3" >&2
  failed=1
}
case_held() {
  local name=$1 tree=$2 want=$3 got
  if got=$(tree_held "$tree"); then got="held ${got:-unread}"; else got=free; fi
  [[ $got == "$want" ]] || fail "$name" "$want" "$got"
}
case_held "a tree that a process works below is held by that process" "$scratch/held" "held $holder"
case_held "a tree that no process works in is free" "$scratch/free" free
case_held "#7502: the caller's own directory is held by the caller" "$scratch/caller" "held $$"
# The landing's shell moves out of the landed tree before it reads, and the
# shell that called it stays there.
moved=$(cd / && held_read && { tree_held "$scratch/caller" || echo free; })
[[ $moved == "$$" ]] || fail "#7502: a shell that moves out leaves its tree held by its parent" "$$" "$moved"
(( failed == 0 )) || exit 1
echo "held cases OK: 4 trees read as their processes hold them, the caller and its parent among them"
