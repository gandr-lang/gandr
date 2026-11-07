#!/usr/bin/env bash
# The unit and the lane that `refactor:file` reads from a branch name (#6012),
# run by `check:claims` over the cases in `branch-unit.json`. Each case runs
# `refactor:file 7 --dry-run` over a stub `gh`. The merged pull request #7
# closes no issue, its head is the case's branch, and its verdict is `yes`
# with one row. The stub answers the area of each unit in the case's `units`,
# and the case's `labels` as the repository's labels. The board holds one
# open collector of each area: `core` is #1, `ci` is #2 and
# `diagnostic-help` is #3. The result names the unit the task read, the lane
# label it read, and the decision, compared with the case's `output`.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
# shellcheck source=../mise/disabled-tools.bash
source "$here/../mise/disabled-tools.bash"
disabled=$(disabled_tools github:cli/cli)
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-branch-unit.XXXXXX")
trap 'rm -rf "$work"' EXIT
failed=0

mkdir "$work/gh"
cat > "$work/gh/gh" << 'STUB'
#!/usr/bin/env bash
printf '%s\n' "$*" >> "$STUB_GH/calls"
case $1 in
  repo) echo gandr-lang/gandr ;;
  api)
    if [[ $2 == graphql ]]; then
      cat "$STUB_GH/pr.json"
    else
      jq -c --arg n "${2##*/}" '.[$n] // {area: null, epic: ""}' "$STUB_GH/units.json"
    fi
    ;;
  label) cat "$STUB_GH/labels.txt" ;;
  issue) cat "$STUB_GH/issues.json" ;;
  *) echo "stub gh: $*" >&2; exit 1 ;;
esac
STUB
chmod +x "$work/gh/gh"
collector() {
  jq -n --argjson number "$1" --arg area "$2" '{number: $number, state: "OPEN", title: "refactor(\($area)): verdicts",
    body: "## Observation\n\n|Kind|Where|Observation|\n|---|---|---|\n|generalise|`a.rs`|an older row|\n\nfrom: #90\n"}'
}
{ collector 1 core; collector 2 ci; collector 3 diagnostic-help; } | jq -s . > "$work/gh/issues.json"

while IFS= read -r case; do
  : > "$work/gh/calls"
  jq -n --arg head "$(jq -r .head <<< "$case")" '{state: "MERGED", headRefName: $head,
    body: "## Refactoring\n\nyes\n\n|Kind|Where|Observation|\n|---|---|---|\n|generalise|`b.rs`|two readers walk one list|\n",
    closingIssuesReferences: {nodes: []}}' > "$work/gh/pr.json"
  jq .units <<< "$case" > "$work/gh/units.json"
  jq -r '.labels[]' <<< "$case" > "$work/gh/labels.txt"
  decision=$(cd "$here" && PATH="$work/gh:$PATH" STUB_GH="$work/gh" GH_BUDGET_TTL=0 MISE_DISABLE_TOOLS="$disabled" \
    mise run --quiet refactor:file 7 --dry-run 2> "$work/err") || true
  unit=$(sed -nE 's|^api repos/[^ ]+/issues/([0-9]+) .*|#\1|p' "$work/gh/calls" | paste -sd ' ' -)
  label=$(sed -nE 's|^label list .*--search ([^ ]+) .*|\1|p' "$work/gh/calls" | paste -sd ' ' -)
  label=${label:+"lane label $label read"}
  got="unit ${unit:-none}; ${label:-no lane label read}; $(jq -r '"\(.act) #\(.issue // "-")"' <<< "$decision" 2> /dev/null || echo "no decision")"
  if [[ $got != "$(jq -r .output <<< "$case")" ]]; then
    printf 'branch-unit case FAILED: %s\n  got: %s\n%s\n' "$(jq -r .name <<< "$case")" "$got" "$(cat "$work/err")" >&2
    failed=1
  fi
done < <(jq -c '.[]' "$here/branch-unit.json")
(( failed == 0 )) || exit 1
echo "branch-unit OK: $(jq length "$here/branch-unit.json") cases read the unit and the lane of each branch form"
