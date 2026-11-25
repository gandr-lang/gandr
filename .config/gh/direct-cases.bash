#!/usr/bin/env bash
# Cases for a read of a task file, and for a read the change adds (#6253).
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
source "$here/../cases/scratch.bash"
check=$here/direct.bash
fail=0
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
piece() { printf '%s%s' "$1" "$2"; }
read_line=$(piece g 'h issue view 1')
pr_line=$(piece g 'h pr view 1')
write_line=$(piece g 'h issue create --title x')

init() {
  rm -rf "$work/repo"
  mkdir -p "$work/repo"
  git -C "$work/repo" init -q
  identity "$work/repo"
  git -C "$work/repo" commit -q --allow-empty -m base
}

commit_file() {
  mkdir -p "$work/repo/$(dirname "$1")"
  printf '%s\n' "$2" > "$work/repo/$1"
  git -C "$work/repo" add -- "$1"
  git -C "$work/repo" commit -q -m add
}

expect_fail() {
  local status=0
  (cd "$work/repo" && "$check" HEAD~1 HEAD) || status=$?
  if [[ $status -eq 1 ]]; then
    printf 'refused: %s\n' "$1"
  else
    printf 'expected a refusal, got %s: %s\n' "$status" "$1" >&2
    fail=1
  fi
}

expect_pass() {
  local status=0
  (cd "$work/repo" && "$check" HEAD~1 HEAD) || status=$?
  if [[ $status -eq 0 ]]; then
    printf 'accepted: %s\n' "$1"
  else
    printf 'expected no refusal, got %s: %s\n' "$status" "$1" >&2
    fail=1
  fi
}

init
commit_file .config/read.bash "$read_line"
expect_fail "an added read with no source"

init
commit_file .config/read.bash "$(printf '%s\n%s' 'source .config/gh/budget.bash' "$read_line")"
expect_pass "a read after the wrapper"

init
commit_file .config/write.bash "$write_line"
expect_pass "an added write"

init
commit_file .config/old.bash "$read_line"
printf '%s\n' '# note' >> "$work/repo/.config/old.bash"
git -C "$work/repo" add -- .config/old.bash
git -C "$work/repo" commit -q -m note
expect_pass "an old read the change does not add"

init
commit_file .config/tasks.toml "$(printf '%s\n' '["one"]' "run = '''" 'source .config/gh/budget.bash' "'''" '["two"]' "run = '''" "$read_line" "'''")"
expect_fail "a read in a task that does not source the wrapper"

init
commit_file .config/tasks.toml "$(printf '%s\n' '["one"]' "run = '''" 'source .config/pr-stack/stack.bash' "$pr_line" "'''")"
expect_pass "a read after stack.bash in the same task"

init
commit_file .config/mise/tasks/mise-tasks-x.toml "$(printf '%s\n' '["one"]' "run = '''" "$read_line" "'''")"
commit_file .config/other.bash '# note'
expect_fail "an old read of a task file that the change does not touch"

init
commit_file .config/mise/tasks/mise-tasks-x.toml "$(printf '%s\n' '["one"]' "run = '''" 'source .config/gh/budget.bash' "$read_line" "'''" '["two"]' "run = '''" "$write_line" "'''")"
commit_file .config/other.bash '# note'
expect_pass "an old read of a task file after the wrapper, and a write in a task with no source"

init
commit_file .config/one/read.bash "$(printf '%s\n' '# the read' "$read_line")"
git -C "$work/repo" mv .config/one .config/two
git -C "$work/repo" commit -q -m move
expect_pass "an old read of a script that the change moves"

init
commit_file .config/old.bash "$(printf '%s\n' 'one=1' 'two=2' 'three=3' 'four=4' "$read_line")"
git -C "$work/repo" mv .config/old.bash .config/new.bash
git -C "$work/repo" commit -q -m rename
expect_pass "an old read in a file the change renames"

init
commit_file .config/old.bash "$(printf '%s\n' 'one=1' 'two=2' 'three=3' 'four=4' 'five=5')"
git -C "$work/repo" mv .config/old.bash .config/new.bash
printf '%s\n' "$read_line" >> "$work/repo/.config/new.bash"
git -C "$work/repo" add -- .config/new.bash
git -C "$work/repo" commit -q -m rename
expect_fail "a read the change adds to a file it renames"

init
commit_file .config/old.bash "$(piece g 'h run list --workflow old.yml')"
commit_file .config/old.bash "$(piece g 'h run list --workflow new.yml')"
expect_pass "a read whose arguments the change edits"

init
commit_file .config/old.bash "$(piece g 'h run list --workflow old.yml')"
commit_file .config/old.bash "$(printf '%s\n%s' "$(piece g 'h run list --workflow new.yml')" "$read_line")"
expect_fail "a read of another command beside an edited read"
((fail == 0))
printf 'gh-direct cases OK\n'
