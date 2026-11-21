#!/usr/bin/env bash
# Check that a landing refusal starts no selected slow check.
#
# - see: #8163
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
failed=0

fail() {
  echo "fast gate case FAILED: $1" >&2
  echo "  got: $2" >&2
  failed=1
}

mkdir "$scratch/bin"
cat > "$scratch/bin/mise" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
printf '%s\n' "$*" >> "$GATE_FAST_TRACE"
if [[ " $* " == *' check:landing '* ]]; then
  printf 'landing checks reached their end\n' >&2
  [[ ${GATE_FAST_REFUSE:-false} == true ]] && exit 1
  exit 0
fi
printf 'slow checks started\n' >&2
EOF
chmod +x "$scratch/bin/mise"

status=0
PATH="$scratch/bin:$PATH" GATE_FAST_TRACE="$scratch/refused.trace" GATE_FAST_REFUSE=true \
  bash "$here/check-run.bash" "$scratch/refused.log" check:landing check:slow > "$scratch/refused.out" 2>&1 || status=$?
[[ $status == 1 && $(< "$scratch/refused.trace") == *'--continue-on-error check:landing'* && $(< "$scratch/refused.trace") != *check:slow* && $(< "$scratch/refused.out") == *'landing checks reached their end'* ]] \
  || fail "#8163: a landing refusal completes its checks and starts no slow check" "exit $status, trace $(< "$scratch/refused.trace"), out $(< "$scratch/refused.out")"

status=0

PATH="$scratch/bin:$PATH" GATE_FAST_TRACE="$scratch/passed.trace" \
  bash "$here/check-run.bash" "$scratch/passed.log" check:landing check:slow-a check:slow-b > "$scratch/passed.out" 2>&1 || status=$?
[[ $status == 0 && $(< "$scratch/passed.trace") == $'run --output prefix --continue-on-error check:landing\nrun --output prefix check:slow-a ::: check:slow-b' ]] \
  || fail "#8163: a landing pass starts every selected slow check after its fast phase" "trace $(< "$scratch/passed.trace")"

(( failed == 0 )) || exit 1
echo "fast gate check OK: a landing refusal completes its checks and starts no slow check"
