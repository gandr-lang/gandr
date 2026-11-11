#!/usr/bin/env bash
# Prints the package arguments of the enforcing suite that `mise run check`
# and the head watcher run, on one line: the whole workspace (#6738). The
# suite of the touched packages alone (#6595) passed two landings of
# 2026-11-11 that turned a test of an untouched package red on `landing`:
# #6709 (#6722) and #6712 (#6736). The adequacy witnesses keep the touched
# scope (`scope.bash --touched`).
#
# Usage: test-scope.bash
set -euo pipefail
echo --workspace
