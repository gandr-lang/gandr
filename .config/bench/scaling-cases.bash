#!/usr/bin/env bash
# The pass of the scaling account (#6879) over a stand-in for the wide host's
# measure command. A measure that reads its stdin to the end, as ssh does,
# still runs the hotpath series at each width of the curve. A measure that
# fails writes no row and pages once for its head, and a second pass over the
# same head sends no second page. The cases read no issue: `issue_found`
# answers that no account is open.
set -euo pipefail
root=$(git rev-parse --show-toplevel)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
export XDG_STATE_HOME=$scratch/state
failed=0
fail() {
  printf 'scaling: %s\n' "$*" >&2
  failed=1
}

# The stand-in reads its stdin to the end and logs each call. It exits with
# `$SCALING_CASE_STATUS`, and gives the curve, a build or a run as the wide
# host's measure command prints them.
cat > "$scratch/measure" << 'EOF'
#!/usr/bin/env bash
cat > /dev/null
echo "$*" >> "$SCALING_CASE_CALLS"
(( ${SCALING_CASE_STATUS:-0} == 0 )) || { echo "measure: exit $SCALING_CASE_STATUS, wall 1.00 s"; exit "$SCALING_CASE_STATUS"; }
case " $* " in
  *" curve "*)
    printf 'measure: commit %s, NUMA nodes all, mutation run idle\n|Threads|Nodes|Wall times (s)|Median (s)|Speed-up|\n|---|---|---|---|---|\n|1|0|6.00 6.00 6.00|6.00|1.00|\n|16|0|3.00 3.00 3.00|3.00|2.00|\n|32|0-1|2.00 2.00 2.00|2.00|3.00|\n|64|0-3|1.50 1.50 1.50|1.50|4.00|\n' "$1" ;;
  *" --no-run "*) echo "cargo: exit 0, wall 1.00 s" ;;
  *) echo "gandr: exit 0, wall 4.50 s" ;;
esac
EOF
chmod +x "$scratch/measure"
export SCALING_CASE_CALLS=$scratch/calls

# shellcheck source=/dev/null
source "$root/.config/issues/keep.bash"
# shellcheck source=.config/bench/scaling.bash
source "$root/.config/bench/scaling.bash"
issue_found() { echo null; }
config=$(jq -n -c --arg measure "$scratch/measure" '{measure: [$measure],
  widths: [{threads: 1, nodes: "0"}, {threads: 16, nodes: "0"}, {threads: 32, nodes: "0-1"}, {threads: 64, nodes: "0-3"}],
  placement: {threads: 16, nodes: "0-1"}, interval: 1800, share: 0.2, page: ["echo", "PAGE"]}')
head=$(git rev-parse HEAD)

# A measure that reads its stdin: one call for the curve, three for the
# placement, one build and one run of the hotpath series at each width.
: > "$SCALING_CASE_CALLS"
row=$(scaling_measure "$head" < /dev/null)
calls=$(wc -l < "$SCALING_CASE_CALLS")
walls=$(jq '.hotpath | length' <<< "$row")
(( calls == 9 && walls == 4 )) || fail "a measure that reads its stdin gives $calls calls and $walls hotpath walls, not 9 and 4"

# A measure that fails: no row, one page for the head, then no second page.
: > "$SCALING_CASE_CALLS"
pages=0
for _ in 1 2; do
  status=0
  out=$(SCALING_CASE_STATUS=101 scaling_once "$head" "" 2>&1 < /dev/null) || status=$?
  (( status == 1 )) || fail "a failed measure gives the status $status, not 1"
  pages=$(( pages + $(grep -c '^PAGE ' <<< "$out" || true) ))
done
(( pages == 1 )) || fail "two passes over a failed measure send $pages pages, not 1"
jq -e --arg key "measure:$head" '.paged == [$key]' "$XDG_STATE_HOME/gandr/scaling.json" > /dev/null \
  || fail "the memory does not hold the one key measure:$head"

(( failed == 0 )) || exit 1
echo "scaling OK: a measure that reads its stdin runs the hotpath series at each width, and a failed measure pages once for its head"
