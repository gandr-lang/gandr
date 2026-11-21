#!/usr/bin/env bash
# Sends the records of a pushed branch's tree to its remote. Prek runs it at
# `pre-push`, after the commit rules accept the branch. A deletion, tag or
# other non-branch ref has no tree that a job reads. A failed record send does
# not block the branch push. The hosted job then runs its check again.
# - see: #8166
set -euo pipefail
head=${PRE_COMMIT_TO_REF:-}
[[ -n $head && ! $head =~ ^0+$ ]] || exit 0
[[ ${PRE_COMMIT_REMOTE_BRANCH:-refs/heads/} == refs/heads/* ]] || exit 0
here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
"$here/verdict.bash" publish "$head" \
  || echo "verdict: the records of the pushed head were not sent, so the hosted jobs run their checks again (#8166)" >&2
