#!/usr/bin/env bash
# A red run pages the fixer once. A second run of the same reading sends
# nothing. The pager is a stub, and the forge is a fixture.
set -euo pipefail
root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/bin" "$work/state"
printf '%s\n' '{"runners":null}' > "$work/runners.json"
jq -n '{workflow_runs: [{name: "riscv64", conclusion: "failure", status: "completed", id: 43228633358, created_at: "2026-11-12T13:34:43Z"}]}' > "$work/runs.json"
cat > "$work/bin/page" <<'EOF'
#!/usr/bin/env bash
printf '%s\n' "$*" >> "$PAGE_LOG"
EOF
chmod +x "$work/bin/page"
export HOSTS_RUNNERS_FILE=$work/runners.json
export HOSTS_RUNS_FILE=$work/runs.json
export HOSTS_STATE_DIR=$work/state
export HOSTS_NOW=1763000000
export GANDR_PAGE=$work/bin/page
export PAGE_LOG=$work/paged
: > "$PAGE_LOG"
out=$("$root/.config/hosts/hosts.bash")
printf '%s\n' "$out" | grep -q 'run riscv64 failed 43228633358' || { echo "hosts page case FAILED: the block names no failed run" >&2; exit 1; }
[[ $(wc -l < "$PAGE_LOG") -eq 1 ]] || { echo "hosts page case FAILED: the first run did not page once" >&2; exit 1; }
grep -q 'RUN riscv64 43228633358' "$PAGE_LOG" || { echo "hosts page case FAILED: the page names no run" >&2; exit 1; }
"$root/.config/hosts/hosts.bash" > /dev/null
[[ $(wc -l < "$PAGE_LOG") -eq 1 ]] || { echo "hosts page case FAILED: the second run paged again" >&2; exit 1; }
echo "hosts page case OK: a red run pages once"
