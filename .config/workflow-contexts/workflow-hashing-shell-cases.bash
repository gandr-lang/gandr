#!/usr/bin/env bash
set -euo pipefail

fail() {
  printf 'workflow hashing shell check FAILED: %s\n' "$1" >&2
  exit 1
}

sh -c 'mise run check:workflow-hashing' || fail "#6413: the workflow hashing task needs its Bash interpreter"
echo 'workflow hashing shell check OK: the task runs from sh through its Bash interpreter'
