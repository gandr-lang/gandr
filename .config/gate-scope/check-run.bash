#!/usr/bin/env bash
# Run the landing checks before the selected slow checks.
set -euo pipefail

log=${1:?the gate log path is required}
shift

status=0
{ MISE_TASK_TIMINGS=1 mise run --output prefix --continue-on-error check:landing 2>&1 1>&3 3>&- | tee "$log" >&2; } 3>&1 || status=$?
if (( status != 0 )); then
  echo "check: the landing checks refused, so no slow check starts" >&2
  exit "$status"
fi

slow=()
for check in "$@"; do
  [[ $check == check:landing ]] || slow+=("$check" :::)
done
if (( ${#slow[@]} == 0 )); then
  exit 0
fi
{ MISE_TASK_TIMINGS=1 mise run --output prefix "${slow[@]:0:${#slow[@]}-1}" 2>&1 1>&3 3>&- | tee -a "$log" >&2; } 3>&1
