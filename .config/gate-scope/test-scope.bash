#!/usr/bin/env bash
# Prints the package arguments of the enforcing suite that `mise run check`
# and the head watcher run, on one line.
#
# A lane's gate runs the suites of the packages its change touches and of
# the readers of `table.json`, whose tests take the corpus as their input
# (`scope.bash --touched --readers`, #6812). `gandr-surface-dispatcher` and
# the run stage `gandr-surface-evaluate` run the whole pipeline. The two
# reds of untouched packages that #6709 (#6722) and #6712 (#6736) brought to
# `landing` are tests of the dispatcher. `gandr-surface-grammar` holds the
# highlight goldens and `gandr-surface-parser` holds the recovery sweep
# (#7949). A corpus source moves both, and only the integration cycle ran
# them. The whole suite (#6738) raised the median gate from 210 s to
# 456.5 s, past the two minutes that its rule allows.
#
# The head watcher sets `GATE_TEST_EVERY_RED` (#6750): its suite runs the
# whole workspace, every test past a red one (`--no-fail-fast`), so a red of
# a package that no lane's gate runs still reaches the known-red list, and a
# red that the green head holds too hides no new red of a later landing. A
# lane's gate keeps fail-fast: a lane needs the first red and a short gate.
#
# Usage: test-scope.bash
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
if [[ -n ${GATE_TEST_EVERY_RED:-} ]]; then
  echo --workspace --no-fail-fast
else
  "$here/scope.bash" --touched --readers
fi
