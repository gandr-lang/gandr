#!/usr/bin/env bash
# The commit rules over a range (#2640): every non-merge commit in
# `<base>..<head>` linted by commitlint as CI's format gate lints it, one run
# per commit with `COMMITLINT_COMMIT` naming it, so the identity rule reads
# that commit's own author; a root commit's message is linted alone. With
# `--empty`, a commit whose tree equals its parent's is refused too: a copy of
# a merged commit, flattened by a rebase, carries no change of its own.
#
# Usage: lint.bash <base> <head> [--empty]. Run in the repository whose
# commits are read; `COMMITLINT_CONFIG` names the configuration (the
# checkout's own by default). Prints each refusal and exits 1 on any.
set -euo pipefail
base=${1:?the base the range starts after}
head=${2:?the head the range ends at}
empty=${3:-}
config=${COMMITLINT_CONFIG:-$(git rev-parse --show-toplevel)/commitlint.config.mjs}
commitlint=${COMMITLINT_BIN:-commitlint}
failed=0
while read -r commit; do
  subject=$(git log -1 --format='%h %s' "$commit")
  if git rev-parse --verify --quiet "$commit^" > /dev/null; then
    lint=(env COMMITLINT_COMMIT="$commit" "$commitlint" --config "$config" --from "$commit^" --to "$commit")
    if ! out=$("${lint[@]}" 2>&1); then
      printf 'commit %s fails the commit rules:\n%s\n' "$subject" "$out" >&2
      failed=1
    fi
    if [[ $empty == --empty ]] && git diff --quiet "$commit^" "$commit"; then
      echo "commit $subject changes nothing: an empty commit, such as a copy of a merged commit a rebase flattened; drop it" >&2
      failed=1
    fi
  elif ! out=$(git log -1 --format=%B "$commit" | env COMMITLINT_COMMIT="$commit" "$commitlint" --config "$config" 2>&1); then
    printf 'commit %s fails the commit rules:\n%s\n' "$subject" "$out" >&2
    failed=1
  fi
done < <(git rev-list --reverse --no-merges "$base..$head")
exit "$failed"
