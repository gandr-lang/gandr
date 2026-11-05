#!/usr/bin/env bash
# The landing watcher reads the commits GitHub's rebase would replay empty
# (#4463, `upstream_replays`), run by `check:pr-stack` over the cases in
# `replays.json`. Each case builds a scratch repository: a lower branch of
# one commit under an upper branch with one commit of its own. The case's
# `lower` says what became of the lower before the upper is read against
# main:
# - `rewritten`: it was rewritten, a file added to its commit, and landed
#   squashed, so the upper holds its earlier head;
# - `squashed`: it landed squashed as it stood;
# - `open`: it has not landed;
# - `conflicting`: main changed the lower's line another way.
# The result, compared with the case's `output`, is the subjects the reading
# prints, joined by `, `, or `none`.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
source "$here/stack.bash"
cases=$here/replays.json
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-replays.XXXXXX")
trap 'rm -rf "$work"' EXIT
failed=0

source "$here/../cases/scratch.bash"

# Land the lower on main squashed: its tree as one new commit. The commit is
# dated apart, or one made in the lower's second would be the lower's itself.
land() {
  git restore --source=lower --staged --worktree .
  git commit --quiet --date=2000-01-01T00:00:00 --message 'lower (#1)'
}

# The scratch stack in `$1`, its lower `$2`.
scenario() {
  git init --quiet --initial-branch=main "$1"
  cd "$1"
  identity
  commit a.txt base base
  git switch --quiet --create lower
  commit a.txt "$(printf 'base\none')" 'lower (#1)'
  git switch --quiet --create upper
  commit u.txt own "upper's own"
  git switch --quiet main
  case $2 in
    rewritten)
      git switch --quiet lower
      printf 'two\n' > b.txt
      git add b.txt
      git commit --quiet --amend --message 'lower (#1), rewritten'
      git switch --quiet main
      land
      ;;
    squashed)
      land
      ;;
    conflicting)
      commit a.txt "$(printf 'base\nelse')" 'main elsewhere'
      ;;
  esac
}

count=$(jq length "$cases")
for (( i = 0; i < count; i++ )); do
  name=$(jq -r ".[$i].name" "$cases")
  expected=$(jq -r ".[$i].output" "$cases")
  lower=$(jq -r ".[$i].lower" "$cases")
  dir=$work/$i
  ( scenario "$dir" "$lower" )
  actual=$(cd "$dir" && upstream_replays main upper | paste -sd ',' - | sed 's/,/, /g')
  [[ -n $actual ]] || actual=none
  if [[ $actual != "$expected" ]]; then
    printf 'pr-stack replay case %s\n  expected: %s\n  actual:   %s\n' "$name" "$expected" "$actual" >&2
    failed=1
  fi
done
(( failed == 0 )) || exit 1
echo "pr-stack replays OK: $count cases read the commits a rebase replays empty as recorded"
