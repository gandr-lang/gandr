#!/usr/bin/env bash
# The issues that a `spelling: replaces` line of a body cites (#6876, #7138):
# one number on each line, each once, in order. A body with no such line
# gives nothing and exits 0, so `pr:open` goes on. `pr:open` asks GitHub
# which of the issues stand open, and `opening.jq` reads them as `spelled`.
#
# Usage: spelled.bash <body>
set -euo pipefail
body=${1:?usage: spelled.bash <body>}
awk '/spelling:[[:space:]]*replaces/ {
  while (match($0, /#[0-9]+/)) {
    print substr($0, RSTART + 1, RLENGTH - 1)
    $0 = substr($0, RSTART + RLENGTH)
  }
}' "$body" | sort -un
