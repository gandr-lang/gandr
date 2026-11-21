#!/usr/bin/env bash
# `pr:open --findings` gives the findings of a body before the gate, run by
# `check:claims`. A queue calls it before it accepts an entry, so a refusal
# costs seconds and no build.
#
# Each case runs the task in a scratch repository with a local bare origin.
# The repository holds a copy of the tree's rules and its concerns, and the
# branch `own` adds one file. A stub of `gh` answers one issue and records
# each call. No case pushes, and no case opens a pull request.
#
# | Case | Exit | Output |
# | --- | --- | --- |
# | a body that lacks parts, on a signed issue | 2 | one refusal line for each rule |
# | a whole body, on an issue with no `shape:signed` | 0 | the `wait:` line and its `arm:` line |
# | a whole body, on a signed issue | 0 | nothing |
set -euo pipefail
root=$(cd "${BASH_SOURCE[0]%/*}/../.." && pwd)
source "$root/.config/cases/scratch.bash"
source "$root/.config/mise/disabled-tools.bash"
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-findings.XXXXXX")
trap 'rm -rf "$work"' EXIT
failed=0

fail() {
  printf 'findings case FAILED: %s\n  got: %s\n' "$1" "$2" >&2
  failed=1
}

# The scratch origin and its clone. The trunk holds the copy of the tree's
# rules, and `own` adds one file past it.
git init --quiet --bare --initial-branch=landing "$work/origin.git"
repo=$work/repo
git init --quiet --initial-branch=landing "$repo"
identity "$repo"
(cd "$root" && git ls-files -z -- .config ledger/concerns.sql | tar -c --null -T - -f -) | tar -x -C "$repo" -f -
git -C "$repo" add -A && git -C "$repo" commit --quiet --no-verify -m base
git -C "$repo" remote add origin "$work/origin.git"
git -C "$repo" push --quiet origin landing
git -C "$repo" checkout --quiet -b own
(cd "$repo" && commit notes.txt 'a note' 'docs: a note')

# The issue of the cases, whole in its sections. Its `## Concerns` names each
# concern of the ledger, as `unit:check` asks.
concerns=$({ cat "$repo/ledger/concerns.sql"; printf '%s\n' "SELECT '|\`' || id || '\`|no — not this case''s|' FROM concern ORDER BY id;"; } | sqlite3 -batch)
axes=(Identity:univalent Locality:oracle Locality:descent Place:located Place:resident Dimension:rewriting Cost:zero-cost Cost:bounded Names:nominal Level:general)
{
  printf 'Text.\n\n## Sources\n\n|Source|Role|What it gives|\n|---|---|---|\n|`next.jq`|primary|the pick|\n\n'
  printf '## Readings\n\n|Family|Axis|Selected|\n|---|---|---|\n'
  for axis in "${axes[@]}"; do printf '|%s|`%s`|no — not this case'"'"'s|\n' "${axis%%:*}" "${axis#*:}"; done
  printf '\n## Concerns\n\n|Concern|Touched|\n|---|---|\n%s\n\n' "$concerns"
  printf '## Engineering\n\n|Row|Bound|\n|---|---|\n'
  for row in change complexity latency parallelism memory failure streaming; do printf '|%s|n/a — not this case'"'"'s|\n' "$row"; done
  printf '\n## Ledger\n\nNone.\n\n## Not in this slice\n\nNothing.\n\n## After\n\nnone\n'
} > "$work/issue.md"

# The stub answers the issue of the cases with the labels of the case, and
# each other read with nothing. `pr view` finds no pull request.
mkdir -p "$work/gh"
cat > "$work/gh/gh" << 'STUB'
#!/usr/bin/env bash
printf '%s\n' "$*" >> "$STUB_GH/calls"
filter=.
for (( i = 1; i <= $#; i++ )); do
  if [[ ${!i} == --jq ]]; then j=$((i + 1)); filter=${!j}; fi
done
case $1 in
  api)
    if [[ " $* " == *" repos/gandr-lang/gandr/issues/7 "* ]]; then
      jq -n --rawfile body "$STUB_GH/issue.md" --argjson labels "$(< "$STUB_GH/labels")" \
        '{number: 7, state: "open", body: $body, labels: [$labels[] | {name: .}]}' | jq -r "$filter"
    else
      jq -rn "[] | $filter"
    fi
    ;;
  *) exit 1 ;;
esac
STUB
chmod +x "$work/gh/gh"
cp "$work/issue.md" "$work/gh/issue.md"
disabled=$(disabled_tools github:cli/cli)

# A whole body answers each part that the issue sets.
{
  printf 'Closes #7\n\n## Sources read\n\n- `next.jq` — read: the pick.\n\n## Readings\n\n|Family|Axis|Status|\n|---|---|---|\n'
  for axis in "${axes[@]}"; do printf '|%s|`%s`|not applicable: the case has no construction.|\n' "${axis%%:*}" "${axis#*:}"; done
  printf '\n## Concerns\n\nNone.\n\n## Engineering\n\n|Row|Measured|\n|---|---|\n'
  for row in change complexity latency parallelism memory failure streaming; do printf '|%s|n/a — not this case'"'"'s|\n' "$row"; done
  printf '\n## Ledger\n\nNone.\n\n## Refactoring\n\nno\n'
} > "$work/whole.md"
printf 'Closes #7\n\n## Sources read\n\n- `next.jq` — the pick.\n\n## Ledger\n\nNone.\n' > "$work/lacking.md"

# Runs `pr:open --findings` on the body `$1` with the labels `$2`. Prints the
# exit, then the findings. The task prints them on standard output. Its
# standard error goes to `err`, where `mise` warns of the moved
# `XDG_CONFIG_HOME`.
findings() {
  local status=0 out
  printf '%s\n' "$2" > "$work/gh/labels"
  cp "$work/$1" "$work/body.md"
  out=$(cd "$root" && PATH="$work/gh:$PATH" STUB_GH="$work/gh" GH_TOKEN=case GH_REPO=gandr-lang/gandr GH_BUDGET_TTL=0 \
    MISE_DISABLE_TOOLS="$disabled" XDG_CONFIG_HOME="$work/config" XDG_CACHE_HOME="$work/cache" GANDR_TRUNK=landing \
    GIT_DIR="$repo/.git" GIT_WORK_TREE="$repo" mise run --quiet pr:open --findings 'docs: a note' "$work/body.md" 2> "$work/err") || status=$?
  printf 'exit %s\n%s\n' "$status" "$out"
}

signed='["kind:feature","area:workflow","shape:signed"]'
unsigned='["kind:feature","area:workflow"]'

# A body that lacks parts is refused with each rule: the source with no
# disposition, the readings and the refactoring. The first line of each
# refusal names its rule.
got=$(findings lacking.md "$signed" | awk '/^exit / || /^the / { sub(/:.*/, ""); print }')
want='exit 2
the `## Sources read` item `- `next.jq` — the pick.` has no disposition
the body'"'"'s `## Readings` leaves an axis unanswered
the body lacks `## Refactoring`
the body lacks `## Engineering`, which #7 states'
[[ $got == "$want" ]] || fail "--findings refuses a body that lacks parts with each rule, exit 2" "$got"

# An issue with no `shape:signed` is a wait, never a refusal.
got=$(findings whole.md "$unsigned" | awk '/^exit / || /^(wait|arm): / { sub(/:.*/, ""); print }')
[[ $got == $'exit 0\nwait\narm' ]] || fail "--findings prints the wait of an unsigned issue and exits 0" "$got"

# A whole body on a signed issue has no finding.
got=$(findings whole.md "$signed")
[[ $got == 'exit 0' ]] || fail "--findings prints nothing for a whole body on a signed issue and exits 0" "$got"

# The origin holds no branch of a case, and no case asks GitHub to open a
# pull request.
pushed=$(git -C "$work/origin.git" for-each-ref --format='%(refname:short)' refs/heads | paste -sd ' ' -)
[[ $pushed == landing ]] || fail "--findings pushes nothing" "$pushed"
! awk '$1 == "pr" && $2 != "view"' "$work/gh/calls" | grep -q . || fail "--findings opens no pull request" "$(awk '$1 == "pr"' "$work/gh/calls")"

(( failed == 0 )) || exit 1
echo "findings check OK: 3 cases refuse a body that lacks parts with exit 2, wait on an unsigned issue with exit 0, pass a whole body, and push and open nothing"
