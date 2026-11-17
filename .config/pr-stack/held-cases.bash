#!/usr/bin/env bash
# The cases of `held.bash` (#6837), over live processes. A process that runs
# in a scratch tree, or below it, holds that tree, and `tree_held` names its
# pid. A tree that no process works in is free. The caller works in a third
# tree, which it holds. A shell that moves to `/` before it reads, as a
# landing moves to the primary worktree, leaves its parent in that tree, and
# the parent holds it. A delete that cannot take one file keeps its tree in
# one line that names the file, and a delete that takes each file goes.
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
# Root deletes any file, and the CI image runs as root. So a stand-in `rm`
# fails on one file, as `rm -rf` fails on a file of another user: it deletes
# each other file and each emptied directory, and the one file stays.
locked=$scratch/locked/target/debug/incremental
undeletable=$locked/unit/root-owned
mkdir -p "$locked/unit" "$scratch/open/target/debug/incremental/unit"
: > "$undeletable"
: > "$locked/unit/own"
: > "$scratch/open/target/debug/incremental/unit/own"
rm() {
  local path
  shift
  for path in "$@"; do
    find "$path" -type f ! -path "$undeletable" -delete
    find "$path" -depth -type d -empty -delete
  done
  for path in "$@"; do [[ ! -e $path ]] || return 1; done
}
status=0
line=$(tree_delete "$scratch/locked (lane)" "the cache clear" "$locked") || status=$?
opened=0
tree_delete "$scratch/open (lane)" "the cache clear" "$scratch/open/target/debug/incremental" > /dev/null || opened=$?
unset -f rm
[[ "$status: $line" == "1: kept $scratch/locked (lane): the cache clear cannot delete $undeletable" ]] \
  || fail "#7533: a file that the caller cannot delete keeps its tree, named in one line" \
    "1: kept $scratch/locked (lane): the cache clear cannot delete $undeletable" "$status: $line"
[[ ! -e $locked/unit/own ]] || fail "#7533: the delete takes each file that it can" "no $locked/unit/own" "it stays"
[[ $opened == 0 && ! -e $scratch/open/target/debug/incremental ]] \
  || fail "a delete that takes each file goes, with no line" "0, no incremental" "$opened, $(ls "$scratch/open/target/debug" 2> /dev/null)"
(( failed == 0 )) || exit 1
echo "held cases OK: 4 trees read as their processes hold them, the caller and its parent among them; a delete that cannot take one file keeps its tree in one line"
