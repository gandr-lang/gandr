#!/usr/bin/env bash
# Lists each entry that a merge group lands, oldest first: one line of the
# merge commit, the pull request number and the pull request's head. The
# queue of `landing` groups by `HEADGREEN`, so a green group lands every
# entry below it. A queue step that reads the title or the body of `HEAD`
# alone then passes each entry under the top one (#6839): pull request 6835
# landed with a red account under the green group of 6836. Each such step
# reads the entries that this script lists.
#
# The entries are the commits on the first-parent line from `<base>`, the
# group's `merge_group.base_sha`, to `HEAD`. Each is the queue's merge of one
# pull request: its second parent is the pull request's head, and its subject
# ends in ` (#N)`.
#
# With `--fetch <rev>`, it first fetches `<rev>` from `origin`, deep enough to
# reach `<base>`, into a shallow checkout.
#
# Usage: entries.bash [--fetch <rev>] <base>
# Exits 2 when the history does not reach `<base>`, when the group lands no
# entry, or when an entry is no merge that names its pull request.
set -euo pipefail
fetch=
if [[ ${1:-} == --fetch ]]; then fetch=${2:?--fetch takes a revision}; shift 2; fi
base=${1:?usage: entries.bash [--fetch <rev>] <base>}
reached() { git cat-file -e "$base^{commit}" 2> /dev/null && git merge-base --is-ancestor "$base" HEAD 2> /dev/null; }
if [[ -n $fetch ]]; then
  # A group holds at most the queue's 10 entries to build; each deepening
  # reads 10 more commits of the first-parent line and their parents.
  git fetch --quiet --no-tags --depth=2 origin "$fetch"
  for _ in 1 2 3; do
    reached && break
    git fetch --quiet --no-tags --deepen=10 origin "$fetch"
  done
fi
reached || { echo "queue: the history does not reach the group's base $base" >&2; exit 2; }
mapfile -t merges < <(git rev-list --reverse --first-parent "$base..HEAD")
(( ${#merges[@]} )) || { echo "queue: the group lands no entry past $base" >&2; exit 2; }
for merge in "${merges[@]}"; do
  head=$(git rev-parse --verify --quiet "$merge^2") \
    || { echo "queue: $merge is no merge of a pull request" >&2; exit 2; }
  number=$(git log -1 --format=%s "$merge" | sed -nE 's/.* \(#([0-9]+)\)$/\1/p')
  [[ -n $number ]] || { echo "queue: the subject of $merge names no pull request" >&2; exit 2; }
  printf '%s %s %s\n' "$merge" "$number" "$head"
done
