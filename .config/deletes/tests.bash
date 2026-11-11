#!/usr/bin/env bash
# Prints each test of both sides whose lines differ, as a JSON array of
# `{id, name}`. `<items-base>` and `<items-head>` are the inventories of
# `check.bash`: `{id, kind, file, start, end, test}`, each file at its path
# in the tree (`paths.jq`). The text before is read from `<base>` with
# `git show`, and the text after from the work tree. A file that the base
# does not hold stops the run with exit 2, since an empty text would read as
# a change (#6844). A test whose file is null comes from a source that a
# build script writes: git holds no text of it, so it is not compared.
#
# Usage: tests.bash <base> <items-base> <items-head>
set -euo pipefail
base=${1:?tests.bash takes the base}
items_base=${2:?tests.bash takes the base inventory}
items_head=${3:?tests.bash takes the head inventory}
root=$(git rev-parse --show-toplevel)
jq -c --slurpfile head "$items_head" \
  '($head[0] | map(select(.test)) | map({key: .id, value: .}) | from_entries) as $h | .[] | select(.test) | select($h[.id] != null) | [., $h[.id]] | select(.[0].file != null and .[1].file != null)' "$items_base" \
  | while IFS= read -r pair; do
    read -r ofile ostart oend nfile nstart nend < <(jq -r '"\(.[0].file) \(.[0].start) \(.[0].end) \(.[1].file) \(.[1].start) \(.[1].end)"' <<< "$pair")
    before=$(git show "$base:$ofile") || { echo "check:deletes: the base $base holds no $ofile, the file of a test" >&2; exit 2; }
    if [[ $(sed -n "${ostart},${oend}p" <<< "$before") != "$(sed -n "${nstart},${nend}p" "$root/$nfile")" ]]; then
      jq -c '.[0] | {id, name: (.id | sub("^.*::"; ""))}' <<< "$pair"
    fi
  done | jq -s -c .
