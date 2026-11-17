#!/usr/bin/env bash
# A scoped command runs whatever the length of its words. The case passes
# `scope` 2,000 words of 100 bytes each, 200 KiB in all, as `xargs` passes a
# large batch. Linux refuses one argument longer than 128 KiB, so a
# description that copies the whole command fails before the command runs.
# The case reads that the command runs and sees each word.
# - see: #7942
set -euo pipefail
root=$(git rev-parse --show-toplevel)
failed=0

fail() {
  echo "scope case FAILED: $1"
  echo "  got: $2"
  failed=1
}

words=()
for index in $(seq 1 2000); do
  words+=("$(printf 'w%099d' "$index")")
done
status=0
out=$("$root/.config/mise/scope" bash -c 'echo "$#"' count "${words[@]}" 2>&1) || status=$?
if [[ $status != 0 || $out != 2000 ]]; then
  fail "#7942: a command of 2000 words of 100 bytes runs in its scope and sees each word" "exit $status: ${out:0:400}"
fi

(( failed == 0 )) || exit 1
echo "scope case OK: a command of 200 KiB of words runs in its scope and sees each word"
