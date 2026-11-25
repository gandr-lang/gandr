#!/usr/bin/env bash
# Reads the body of each pull request that a merge group lands, as it stands,
# into `<dir>/<number>.md` (#6839, #6883). The queue's steps read each entry's
# body: the account of what it takes out (`.config/deletes/queue.bash`) and
# the issues it closes (`check:ledger`). So one read of each body serves them
# all: gh makes one REST read for each entry.
#
# `<entries>` is the output of `.config/queue/entries.bash`.
#
# Usage: bodies.bash <entries> <dir>
# Exits 2 on a failed read, after it reads every entry.
set -euo pipefail
entries=${1:?usage: bodies.bash <entries> <dir>}
dir=${2:?usage: bodies.bash <entries> <dir>}
mkdir -p "$dir"
status=0
while read -r _ number _; do
  if ! gh api "repos/{owner}/{repo}/pulls/$number" --jq '.body // ""' > "$dir/$number.md" < /dev/null; then
    echo "queue: the body of pull request #$number does not read" >&2
    rm -f "$dir/$number.md"
    status=2
  fi
done < "$entries"
exit "$status"
