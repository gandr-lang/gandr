#!/usr/bin/env bash
# `epics:link` over a stubbed `gh` (#5688), run by `check:issues`. The stub
# answers the two GraphQL reads the task makes: every issue, in two pages,
# and the open issues' graph of `deps_open_graph`. It also answers the free
# `rate_limit` gauge of `budget.bash`. Any other call is refused, so a REST
# list read fails the case. The dry run prints the plan and sets nothing.
set -euo pipefail
# shellcheck source=../mise/disabled-tools.bash
source "${BASH_SOURCE[0]%/*}/../mise/disabled-tools.bash"
disabled=$(disabled_tools github:cli/cli)
work=$(mktemp -d "${TMPDIR:-/tmp}/gandr-epics-link.XXXXXX")
trap 'rm -rf "$work"' EXIT
mkdir "$work/bin" "$work/pages"
failed=0

fail() {
  echo "epics:link case FAILED: $1"
  echo "  got: $2"
  failed=1
}

# Every issue, newest first, in two pages of the shape the query reads.
jq -n -c '{data: {repository: {issues: {nodes: [
  {number: 30, state: "OPEN", body: "The units: #31 and #32.", labels: {nodes: [{name: "kind:epic"}]}},
  {number: 32, state: "CLOSED", body: "x", labels: {nodes: [{name: "kind:feature"}]}},
  {number: 31, state: "OPEN", body: "Part of #30.", labels: {nodes: [{name: "kind:defect"}]}}]}}}}' > "$work/pages/issues-1.json"
jq -n -c '{data: {repository: {issues: {nodes: [
  {number: 22, state: "OPEN", body: "A row on #20.", labels: {nodes: [{name: "collector"}]}},
  {number: 21, state: "OPEN", body: "after #20", labels: {nodes: [{name: "kind:feature"}]}},
  {number: 20, state: "OPEN", body: "none", labels: {nodes: [{name: "kind:epic"}]}}]}}}}' > "$work/pages/issues-2.json"
# The open issues' graph: #30 is blocked by #31 already.
jq -n -c '[30, 31, 22, 21, 20] | {data: {repository: {issues: {nodes: map({number: .,
  blockedBy: (if . == 30 then {totalCount: 1, nodes: [{number: 31, state: "OPEN"}]} else {totalCount: 0, nodes: []} end),
  subIssues: {totalCount: 0, nodes: []}})}}}}' > "$work/pages/graph-1.json"

cat > "$work/bin/gh" << 'EOF'
#!/usr/bin/env bash
call="$*"
printf '%s\n' "$call" >> "$STUB_PAGES/calls"
# Only whether the token is the case's own, so no real token reaches a log.
if [[ ${GH_TOKEN-} == case ]]; then echo case; elif [[ -z ${GH_TOKEN-} ]]; then echo unset; else echo another; fi >> "$STUB_PAGES/tokens"
if [[ $1 == api && $2 == rate_limit ]]; then echo 0; exit 0; fi
query= expr=
while (($#)); do
  case $1 in
    -f) [[ $2 == query=* ]] && query=${2#query=}; shift 2 ;;
    --jq) expr=$2; shift 2 ;;
    *) shift ;;
  esac
done
case $query in
  *blockedBy*) pages=("$STUB_PAGES"/graph-*.json) ;;
  *'labels(first'*) pages=("$STUB_PAGES"/issues-*.json) ;;
  *) echo "gh stub: unexpected $call" >&2; exit 1 ;;
esac
for page in "${pages[@]}"; do jq -c "$expr" "$page"; done
EOF
chmod +x "$work/bin/gh"
# The stub reads no token. A host can put a `gh` wrapper first on `PATH`,
# and with no `GH_TOKEN` that wrapper asks the next `gh`, the stub, for one
# (#6632). So the case sets a token of its own.
export GH_TOKEN=case

status=0
output=$(STUB_PAGES=$work/pages GH_REPO=case/case GH_BUDGET_TTL=0 XDG_CACHE_HOME=$work/cache PATH="$work/bin:$PATH" \
  MISE_DISABLE_TOOLS="$disabled" \
  mise run --quiet epics:link --dry-run 2> "$work/err") || status=$?
expected=$'#30: would add 1; 1 open of 2 blocked-by\n#20: would add 1; 1 open of 1 blocked-by\nepics:link: 2 open epic(s) read; 0 dependency(ies) refused'
[[ $status == 0 && $output == "$expected" ]] \
  || fail "#5688: epics:link plans each open epic from the GraphQL reads, newest first, with no REST list read" \
    "exit $status: $output $(< "$work/err")"
reads=$(awk '$1 == "api" && $2 != "rate_limit" { print $2 }' "$work/pages/calls" | sort | uniq -c | awk '{ print $2 "=" $1 }' | paste -sd ' ' -)
[[ $reads == "graphql=2" ]] \
  || fail "#5688: epics:link makes two GraphQL reads, the issues and the open graph, and no REST read" "$reads"
tokens=$(sort -u "$work/pages/tokens" | paste -sd ' ' -)
[[ $tokens == "case" ]] \
  || fail "#6632: each call reaches the stub with the case's own GH_TOKEN, never the caller's, so a wrapper of the host asks the stub for no token" "$tokens"

(( failed == 0 )) || exit 1
echo "epics:link check OK: the plan is read through GraphQL alone"
