#!/usr/bin/env bash
# Prints the package arguments of the enforcing suite that `mise run check`
# and the head watcher run, on one line: the whole workspace (#6738). The
# suite of the touched packages alone (#6595) passed two landings of
# 2026-11-11 that turned a test of an untouched package red on `landing`:
# #6709 (#6722) and #6712 (#6736). The adequacy witnesses keep the touched
# scope (`scope.bash --touched`).
#
# The head watcher sets `GATE_TEST_EVERY_RED` (#6750): its suite runs every
# test past a red one (`--no-fail-fast`), so a red that the green head holds
# too hides no new red of a later landing. A lane's gate keeps fail-fast: a
# lane needs the first red and a short gate.
#
# Usage: test-scope.bash
set -euo pipefail
if [[ -n ${GATE_TEST_EVERY_RED:-} ]]; then
  echo --workspace --no-fail-fast
else
  echo --workspace
fi
