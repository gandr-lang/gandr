#!/usr/bin/env bash
# The restack replays only a stack's own commits (#3078, #3115), run by
# `check:pr-stack` over the cases in `restacks.json`. Each case builds a
# scratch repository with a local bare origin: a lower branch of three
# commits, each rewriting one line, under an upper branch with one commit of
# its own. The case's `lower` says what became of the lower:
# - `squashed`: it landed squashed into one commit on main and its branch is
#   gone; the stack is the upper alone, and `landed_heads` reads the lower's
#   earlier head as the server would when `held` is true.
# - `rewritten`: it is open and was force-pushed with its last commit
#   changed; the stack is the lower and the upper, and `pushed_heads` reads
#   the lower's earlier head as the server would when `held` is true.
# The restack's result is one line compared with the case's `output`:
# `moved: <the subjects main..upper holds>`, or `refused: <the refusal up to
# its first semicolon>` and `, moved` should the refused restack have moved
# the upper.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
source "$here/stack.bash"
cases=$here/restacks.json
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-own-commits.XXXXXX")
trap 'rm -rf "$work"' EXIT
repo=case/case
trunk=main
failed=0

commit() { printf '%s\n' "$2" > "$1" && git add "$1" && git commit --quiet --message "$3"; }

# The scratch stack in `$1`, its lower `$2` (`squashed` or `rewritten`);
# prints the lower's head the upper was stacked on.
scenario() {
  git init --quiet --bare --initial-branch=main "$1/origin.git"
  git clone --quiet "$1/origin.git" "$1/clone" 2> /dev/null
  cd "$1/clone"
  git config user.name case
  git config user.email case@example.invalid
  git config commit.gpgsign false
  commit a.txt base base
  git push --quiet origin main
  git switch --quiet --create lower
  commit a.txt one 'lower 1'
  commit a.txt two 'lower 2'
  commit a.txt three 'lower 3'
  git rev-parse HEAD
  git switch --quiet --create upper
  commit u.txt own "upper's own"
  git push --quiet origin lower upper
  if [[ $2 == squashed ]]; then
    git switch --quiet main
    git merge --quiet --squash lower > /dev/null
    git commit --quiet --message 'lower (#1)'
    git push --quiet origin main
    git push --quiet origin --delete lower
  else
    git switch --quiet lower
    git reset --quiet --hard HEAD^
    commit a.txt three-again 'lower 3 again'
    git push --quiet --force origin lower
  fi
}

count=$(jq length "$cases")
for (( i = 0; i < count; i++ )); do
  name=$(jq -r ".[$i].name" "$cases")
  expected=$(jq -r ".[$i].output" "$cases")
  lower=$(jq -r ".[$i].lower" "$cases")
  dir=$work/$i
  mkdir "$dir"
  lower_head=$(scenario "$dir" "$lower" | tail -n 1)
  cd "$dir/clone"
  upper_head=$(git rev-parse origin/upper)
  landed_heads() { :; }
  pushed_heads() { :; }
  stack='[{"head":"upper"}]'
  if [[ $lower == rewritten ]]; then stack='[{"head":"lower"},{"head":"upper"}]'; fi
  if [[ $(jq -r ".[$i].held" "$cases") == true ]]; then
    if [[ $lower == squashed ]]; then
      landed_heads() { printf '%s\n' "$lower_head"; }
    else
      pushed_heads() { printf '%s\n' "$lower_head"; }
    fi
  fi
  if restack "$stack" > "$dir/out" 2>&1; then
    actual="moved: $(git log --format=%s origin/main..origin/upper | paste -sd ',' - | sed 's/,/, /g')"
  else
    actual="refused: $(grep -o -E '(conflicts in|[^ ]+ does not contain) [^;]*' "$dir/out" | head -n 1 || true)"
    [[ $(git rev-parse origin/upper) == "$upper_head" ]] || actual+=", moved"
  fi
  cd - > /dev/null
  if [[ $actual != "$expected" ]]; then
    printf 'pr-stack restack case %s\n  expected: %s\n  actual:   %s\n' "$name" "$expected" "$actual" >&2
    sed 's/^/    /' "$dir/out" >&2
    failed=1
  fi
done
(( failed == 0 )) || exit 1
echo "pr-stack restacks OK: $count cases restack as recorded"
