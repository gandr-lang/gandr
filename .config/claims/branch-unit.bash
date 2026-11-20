#!/usr/bin/env bash
# The unit and the lane that `refactor:file` reads from a branch name (#6012),
# run by `check:claims` over the cases in `branch-unit.json`. Each case runs
# `refactor:file 7 --dry-run` over a stub `gh`. The merged pull request #7
# closes no issue, its head is the case's branch, and its verdict is `yes`
# with one row. The stub answers the area of each unit in the case's `units`,
# and the case's `labels` as the repository's labels. The board holds the
# tree's one open collector, #1, with a heading for `core`, `ci` and
# `diagnostic-help`. The result names the unit the task read, the lane label
# it read, and the decision with its labels, compared with the case's
# `output`.
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
jq -n '[{number: 1, state: "OPEN", title: "refactor: verdicts",
  body: (["## Observation", "", (("core", "ci", "diagnostic-help") | "### \(.)\n\n|Kind|Where|Observation|\n|---|---|---|\n|generalise|`a.rs`|an older row of \(.)|\n"), "from: #90", ""] | join("\n"))}]' \
  > "$work/gh/issues.json"

while IFS= read -r case; do
  : > "$work/gh/calls"
  jq -n --arg head "$(jq -r .head <<< "$case")" '{state: "MERGED", headRefName: $head,
    body: "## Refactoring\n\nyes\n\n|Kind|Where|Observation|\n|---|---|---|\n|generalise|`b.rs`|two readers walk one list|\n",
    closingIssuesReferences: {nodes: []}}' > "$work/gh/pr.json"
  jq .units <<< "$case" > "$work/gh/units.json"
  jq -r '.labels[]' <<< "$case" > "$work/gh/labels.txt"
  # The stub reads no token. A host can put a `gh` wrapper first on `PATH`,
  # and with no `GH_TOKEN` that wrapper asks the next `gh`, the stub, for one
  # (#6632, #7521). So the case sets a token of its own.
  decision=$(cd "$here" && PATH="$work/gh:$PATH" GH_TOKEN=case STUB_GH="$work/gh" GH_BUDGET_TTL=0 MISE_DISABLE_TOOLS="$disabled" \
    mise run --quiet refactor:file 7 --dry-run 2> "$work/err") || true
  unit=$(sed -nE 's|^api repos/[^ ]+/issues/([0-9]+) .*|#\1|p' "$work/gh/calls" | paste -sd ' ' -)
  label=$(sed -nE 's|^label list .*--search ([^ ]+) .*|\1|p' "$work/gh/calls" | paste -sd ' ' -)
  label=${label:+"lane label $label read"}
  got="unit ${unit:-none}; ${label:-no lane label read}; $(jq -r '"\(.act) #\(.issue // "-") \(.labels // [] | join(" "))"' <<< "$decision" 2> /dev/null || echo "no decision")"
  if [[ $got != "$(jq -r .output <<< "$case")" ]]; then
    printf 'branch-unit case FAILED: %s\n  got: %s\n%s\n' "$(jq -r .name <<< "$case")" "$got" "$(cat "$work/err")" >&2
    failed=1
  fi
done < <(jq -c '.[]' "$here/branch-unit.json")
(( failed == 0 )) || exit 1
echo "branch-unit OK: $(jq length "$here/branch-unit.json") cases read the unit and the lane of each branch form"
