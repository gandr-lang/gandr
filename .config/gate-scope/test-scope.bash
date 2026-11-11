#!/usr/bin/env bash
# Prints the package arguments of the enforcing suite that `mise run check`
# runs, on one line. A lane's gate runs the suite of the packages its change
# touches (#6595, `scope.bash --touched`). The head watcher sets
# `GATE_TEST_WHOLE` (#6725): no test lane runs after the merge queue, and the
# touched suite passed `f2b3dadaf` over two red tests of a package that the
# change did not touch. Its suite is then the whole workspace.
#
# Usage: test-scope.bash
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
if [[ -n ${GATE_TEST_WHOLE:-} ]]; then
  echo "scope: GATE_TEST_WHOLE is set, so the enforcing suite runs over the whole workspace" >&2
  echo --workspace
else
  "$here/scope.bash" --touched
fi
