#!/usr/bin/env bash
# Refuses a case harness that commits with no scratch identity (#7180). A
# host's global Git configuration can sign each commit and tag through an
# agent that a remote shell cannot reach, so a scratch commit with the
# host's configuration fails the gate on that host (#7159). `identity` of
# `scratch.bash` keeps the host's signing out of a scratch repository.
#
# A committing call is `git` with any options, then `commit`, `tag`,
# `merge`, `cherry-pick`, `revert`, `rebase`, `am` or `commit-tree`, or a
# call of the helper `commit` of `scratch.bash`. A harness with a
# committing call and no call of `identity` is refused, with the path and
# the line of its first committing call. A comment line holds no call.
#
# Usage: identity.bash [<harness>...]; with no argument, each tracked case
# harness, `.config/**/*cases.bash`.
set -euo pipefail
if (( $# == 0 )); then
  mapfile -t harnesses < <(git ls-files -- '.config/**cases.bash')
else
  harnesses=("$@")
fi
refused=0
for harness in "${harnesses[@]}"; do
  verdict=$(awk '
    /^[[:space:]]*#/ { next }
    {
      n = split($0, word, /[[:space:]]+|[;&|(){}]+/)
      for (i = 1; i <= n; i++) {
        if (word[i] == "identity") identity = 1
        if (word[i] == "commit" && (i == 1 || word[i - 1] == "" || word[i - 1] == "&&" || word[i - 1] == "then" || word[i - 1] == "do")) {
          if (!first) first = FNR
        }
        if (word[i] == "git" || word[i] == "\"$git\"") {
          j = i + 1
          while (j <= n && word[j] ~ /^-/) {
            if (word[j] == "-C" || word[j] == "-c") j++
            j++
          }
          if (word[j] ~ /^(commit|tag|merge|cherry-pick|revert|rebase|am|commit-tree)$/ && !first) first = FNR
        }
      }
    }
    END { if (first && !identity) print first }
  ' "$harness")
  if [[ -n $verdict ]]; then
    echo "case identity: $harness:$verdict commits with no call of identity (.config/cases/scratch.bash)" >&2
    refused=1
  fi
done
exit "$refused"
