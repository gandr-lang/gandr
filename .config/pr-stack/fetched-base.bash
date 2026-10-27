#!/usr/bin/env bash
# `pr:open` measures a stacked change from a trunk it has fetched (#3148), run
# by `check:pr-stack` over the cases in `fetched.json`. Each case builds a
# scratch repository with a local bare origin: a lower branch, and an upper
# branch stacked on it. When the case's `merged` is true, the lower then
# merges on the origin, from another clone, after the stack's clone last
# fetched. The stack's clone has no open pull requests to read, so the
# measurement is the merge base with `origin/main`, as `evidence:base` reads
# it then. `measured_from` on the upper names the commit it measures from,
# compared with the case's `output`: `lower`, the lower's head, or `base`, the
# trunk's commit the lower forked from. On a stale trunk a merged lower reads
# `base`, and its paths read as the upper's own.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
source "$here/stack.bash"
cases=$here/fetched.json
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-fetched-base.XXXXXX")
trap 'rm -rf "$work"' EXIT
trunk=main
failed=0

commit() { printf '%s\n' "$2" > "$1" && git add "$1" && git commit --quiet --message "$3"; }
identity() { git config user.name case && git config user.email case@example.invalid && git config commit.gpgsign false; }
evidence_base() { git merge-base origin/main HEAD; }

count=$(jq length "$cases")
for (( i = 0; i < count; i++ )); do
  name=$(jq -r ".[$i].name" "$cases")
  expected=$(jq -r ".[$i].output" "$cases")
  dir=$work/$i
  git init --quiet --bare --initial-branch=main "$dir/origin.git"
  git clone --quiet "$dir/origin.git" "$dir/stack" 2> /dev/null
  cd "$dir/stack"
  identity
  commit a.txt base base
  git push --quiet origin main
  base=$(git rev-parse HEAD)
  git switch --quiet --create lower
  commit l.txt lower 'lower (#1)'
  lower=$(git rev-parse HEAD)
  git switch --quiet --create upper
  commit u.txt upper 'upper (#2)'
  git push --quiet origin lower upper
  if [[ $(jq -r ".[$i].merged" "$cases") == true ]]; then
    git clone --quiet "$dir/origin.git" "$dir/merger" 2> /dev/null
    cd "$dir/merger"
    identity
    git fetch --quiet origin lower
    git merge --quiet --no-ff --message 'Merge #1' origin/lower
    git push --quiet origin main
    cd "$dir/stack"
  fi
  case $(measured_from) in
    "$lower") actual=lower ;;
    "$base") actual=base ;;
    *) actual="another commit" ;;
  esac
  if [[ $actual != "$expected" ]]; then
    printf 'pr-stack fetched-base case %s\n  expected: %s\n  actual:   %s\n' "$name" "$expected" "$actual" >&2
    failed=1
  fi
done
(( failed == 0 )) || exit 1
echo "pr-stack fetched base OK: $count cases measured from a fetched trunk"
