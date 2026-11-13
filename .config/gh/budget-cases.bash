#!/usr/bin/env bash
# The wrapper's cache keeps the answer of a read of the checkout's branch for
# that branch (#7143). A stub `gh` answers `pr view` with the number it names,
# else with the branch it runs on, and logs each call. In one checkout:
#
# - each of two branches reads its own branch, and a second read of a branch
#   comes from the cache;
# - a read that names its pull request runs once for both branches;
# - a read that sets `GH_BUDGET_TTL=0` on its call fetches afresh while the
#   cache holds its answer (#6253).
#
# The cases call the wrapper through `$word`, so `sites.awk` reads no call
# site here.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-budget.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir "$work/bin" "$work/repo"
cat > "$work/bin/gh" << 'EOF'
#!/usr/bin/env bash
set -euo pipefail
echo "$*" >> "$STUB_BUDGET_CALLS"
[[ ${1:-} == pr && ${2:-} == view ]] || { echo "stub: unexpected $*" >&2; exit 1; }
if [[ ${3:-} =~ ^[0-9]+$ ]]; then echo "$3"; else git branch --show-current; fi
EOF
chmod +x "$work/bin/gh"
git -C "$work/repo" init -q -b one
git -C "$work/repo" -c user.name=case -c user.email=case@example.invalid commit -q --allow-empty -m one
git -C "$work/repo" branch two
export GH_TOKEN=case XDG_CACHE_HOME=$work/cache STUB_BUDGET_CALLS=$work/calls PATH=$work/bin:$PATH
unset GH_REPO
: > "$STUB_BUDGET_CALLS"
# shellcheck source=budget.bash
source "$here/budget.bash"
word=$(printf '%s%s' g h)
cd "$work/repo"
failed=0
fail() {
  printf 'budget case FAILED: %s\n' "$1" >&2
  failed=1
}
calls() { awk -v want="$1" '$0 == want' "$STUB_BUDGET_CALLS" | wc -l | tr -d ' '; }

git switch -q one
first=$("$word" pr view --json number)
git switch -q two
second=$("$word" pr view --json number)
git switch -q one
again=$("$word" pr view --json number)
[[ $first == one && $second == two && $again == one ]] \
  || fail "#7143: the branches one, two and one read $first, $second and $again"
[[ $(calls 'pr view --json number') == 2 ]] \
  || fail "#7143: the reads of two branches ran $(calls 'pr view --json number') calls, not 2"

named=$("$word" pr view 7 --json number)
git switch -q two
named_two=$("$word" pr view 7 --json number)
[[ $named == 7 && $named_two == 7 ]] || fail "#7143: the read of #7 gave $named and $named_two"
[[ $(calls 'pr view 7 --json number') == 1 ]] \
  || fail "#7143: the read of #7 ran $(calls 'pr view 7 --json number') calls for two branches, not 1"
GH_BUDGET_TTL=0 "$word" pr view 7 --json number > /dev/null
[[ $(calls 'pr view 7 --json number') == 2 ]] \
  || fail "#6253: a read with GH_BUDGET_TTL=0 on its call ran $(calls 'pr view 7 --json number') calls in all, not 2"

((failed == 0)) || exit 1
echo "budget cases OK: two branches read their own pull request, a branch reads it again from the cache, a read that names its pull request runs once for both, and a read with GH_BUDGET_TTL=0 fetches afresh"
