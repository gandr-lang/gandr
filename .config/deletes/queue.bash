#!/usr/bin/env bash
# Reads the account of every pull request that a merge group lands (#6839).
# The queue of `landing` lands each entry under a green group, so the queue
# step reads each entry's body, not the body of the top entry alone. It runs
# `check.bash --rows-only` for each entry against that pull request's own
# head, the merge's second parent, so the entries ahead of it move no
# sign-off.
#
# `<entries>` is the output of `.config/queue/entries.bash`, and `<bodies>`
# the directory of the entries' bodies that `.config/queue/bodies.bash`
# reads (#6883). An entry whose body did not read is refused.
#
# Usage: queue.bash <entries> <bodies>
# Exits 1 when an entry's account is refused and 2 on a body that did not
# read; it reads every entry before it exits.
set -euo pipefail
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
entries=${1:?usage: queue.bash <entries> <bodies>}
bodies=${2:?usage: queue.bash <entries> <bodies>}
status=0
worst() { (( $1 > status )) && status=$1 || :; }
while read -r merge number head; do
  echo "pull request #$number at ${head:0:9}:"
  if [[ ! -f $bodies/$number.md ]]; then
    echo "queue: the body of pull request #$number did not read" >&2
    worst 2
    continue
  fi
  code=0
  "$here/check.bash" --rows-only --head "$head" "$bodies/$number.md" "$merge^1" < /dev/null || code=$?
  worst "$code"
done < "$entries"
exit "$status"
