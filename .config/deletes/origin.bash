#!/usr/bin/env bash
# The pull request that adds a thing to the tree at a base, for the `Origin`
# of a row of `## Deletes` (#6817): its number, or `null`.
#
#   origin.bash <base> span <file> <start> <end>   the lines of an item
#   origin.bash <base> text <file> <text>          a ledger row or a kept line
#   origin.bash <base> file <path>                 a file
#
# An item names its origin by its own lines: the oldest commit that touches
# them, which `git log -L` follows back through each edit. A word of its name
# elsewhere in the file names no origin: a field's bare name `start` once
# gave a type the pull request that first wrote `start` in that file (#7259).
# A ledger row and a kept line have no span, so the oldest commit that adds or
# removes their text names them. A pull request's number stands at the end of
# its commit's subject, or, for a commit that the merge queue brings in, at
# the end of the subject of the oldest merge that brings it into the base.
set -euo pipefail
base=$1
form=$2
shift 2
commit=
case $form in
  span) commit=$(git log -L "$2,$3:$1" -s --reverse --format=%H "$base" 2> /dev/null | awk 'NF { print; exit }') || commit= ;;
  text) commit=$(git log --reverse --format=%H -S"$2" "$base" -- "$1" 2> /dev/null | awk 'NR == 1') || commit= ;;
  file) commit=$(git log --diff-filter=A --format=%H "$base" -- "$1" 2> /dev/null | awk 'END { print }') || commit= ;;
  *)
    echo "origin.bash: no form $form; span, text or file" >&2
    exit 2
    ;;
esac
[[ -n $commit ]] || { echo null; exit 0; }
subject=$(git log -1 --format=%s "$commit")
if [[ ! $subject =~ \(#[0-9]+\)$ ]]; then
  subject=$(git log --merges --ancestry-path --format=%s "$commit..$base" | awk '/\(#[0-9]+\)$/ { last = $0 } END { print last }')
fi
[[ $subject =~ \(#([0-9]+)\)$ ]] && echo "${BASH_REMATCH[1]}" || echo null
