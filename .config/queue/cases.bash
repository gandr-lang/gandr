#!/usr/bin/env bash
# The cases of the queue's walk over a merge group (#6839), run by
# `check:queue`. The queue of `landing` groups by `HEADGREEN`, so the green
# group of pull request 6836 landed 6835 under it, whose own account was red:
# the queue step read the body of `HEAD` alone. Each case builds a scratch
# history of a base and two queue merges, `(#1)` under `(#2)`, as the queue
# writes them. `entries.bash` lists both entries with their heads.
# `.config/deletes/queue.bash` reads each entry's body through a stub `gh`:
# a group whose lower entry's account is red is refused and names that
# entry, and a group whose accounts are both clean passes. A base that the
# history does not reach, and a merge that names no pull request, are
# refused with exit 2.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-queue-cases.XXXXXX")
trap 'rm -rf "$work"' EXIT
failed=0
fail() {
  echo "queue case FAILED: $1"
  echo "  got: $2"
  failed=1
}

# The scratch history reads the check's `.config` through a link to this
# tree's own.
repo=$work/repo
git init --quiet --initial-branch=landing "$repo"
ln -s "$root/.config" "$repo/.config"
export GIT_AUTHOR_NAME=case GIT_AUTHOR_EMAIL=case@example.invalid GIT_COMMITTER_NAME=case GIT_COMMITTER_EMAIL=case@example.invalid
git -C "$repo" add -A && git -C "$repo" commit --quiet --no-gpg-sign -m 'base'
base=$(git -C "$repo" rev-parse HEAD)
for number in 1 2; do
  git -C "$repo" switch --quiet -c "pr-$number" landing
  echo "$number" > "$repo/file-$number"
  git -C "$repo" add -A && git -C "$repo" commit --quiet --no-gpg-sign -m "change $number"
  git -C "$repo" switch --quiet landing
  git -C "$repo" merge --quiet --no-ff --no-gpg-sign -m "fix(workflow): change $number (#$number)" "pr-$number"
done
heads=("$(git -C "$repo" rev-parse pr-1)" "$(git -C "$repo" rev-parse pr-2)")

# A stub `gh` that answers each body from `$work/bodies/<n>.md`.
mkdir -p "$work/bin" "$work/bodies"
cat > "$work/bin/gh" << 'STUB'
#!/usr/bin/env bash
for arg in "$@"; do
  if [[ $arg =~ pulls/([0-9]+)$ ]]; then cat "$GH_STUB_BODIES/${BASH_REMATCH[1]}.md"; exit 0; fi
done
echo "gh stub: no answer for $*" >&2
exit 1
STUB
chmod +x "$work/bin/gh"
export PATH="$work/bin:$PATH" GH_STUB_BODIES=$work/bodies GH_REPO=case/repo

entries=$(cd "$repo" && "$here/entries.bash" "$base") || entries="exit $?"
want=$(printf '%s 1 %s\n%s 2 %s' "$(git -C "$repo" rev-parse HEAD^)" "${heads[0]}" "$(git -C "$repo" rev-parse HEAD)" "${heads[1]}")
[[ $entries == "$want" ]] || fail "#6839: the walk lists each entry of the group, oldest first, with its head" "$entries"

clean=$'## Deletes\n\nnone\n'
red=$'## Deletes\n\n|Item|Origin|Act|Why|Future use|In place of deletion|After|Witness|Sign-off|\n|---|---|---|---|---|---|---|---|---|\n|`v::Item`|#1|removed|gone|none|none|none|none|none|\n'
run() {
  printf '%s' "$1" > "$work/bodies/1.md"
  printf '%s' "$2" > "$work/bodies/2.md"
  printf '%s\n' "$entries" > "$work/entries"
  status=0
  out=$(cd "$repo" && "$repo/.config/deletes/queue.bash" "$work/entries" 2>&1) || status=$?
}
run "$red" "$clean"
if [[ $status != 1 || $out != *'pull request #1 at'*'says `removed`'*'pull request #2 at'* ]]; then
  fail "#6839: a group whose lower entry's account is red is refused, naming that entry" "status $status: $out"
fi
run "$clean" "$clean"
[[ $status == 0 ]] || fail "#6839: a group whose accounts are both clean passes" "status $status: $out"

status=0
out=$(cd "$repo" && "$here/entries.bash" 0000000000000000000000000000000000000000 2>&1) || status=$?
[[ $status == 2 ]] || fail "#6839: a base that the history does not reach is refused with exit 2" "status $status: $out"
git -C "$repo" commit --quiet --no-gpg-sign --allow-empty -m 'a push outside the queue'
status=0
out=$(cd "$repo" && "$here/entries.bash" "$base" 2>&1) || status=$?
[[ $status == 2 ]] || fail "#6839: a commit that is no merge of a pull request is refused with exit 2" "status $status: $out"

(( failed == 0 )) || exit 1
echo "queue check OK: the walk lists each entry of a group with its head, a red lower entry is refused by name, and an unreached base or a stray commit is refused"
