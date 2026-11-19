#!/usr/bin/env bash
# Stops `check:dylint` in a merge group that names no base (#7632). The
# compiler policy holds each function that a change alters against the base's
# records, and with no base it holds none. A merge group is the one required
# run that reads a change, so there a missing `GATE_BASE` is a fault of the
# workflow and never a pass. Outside a merge group, a run with no base holds the
# crates of the default alone, as `gate:all` does.
#
# Reads `GITHUB_EVENT_NAME` and `GATE_BASE`. Exits 1 by name in a merge group
# with no base, and 0 otherwise.
set -euo pipefail
if [[ ${GITHUB_EVENT_NAME:-} == merge_group && -z ${GATE_BASE:-} ]]; then
  echo "check:dylint: the merge group names no GATE_BASE, so allocation_free_region would hold no changed function (#7632)" >&2
  exit 1
fi
