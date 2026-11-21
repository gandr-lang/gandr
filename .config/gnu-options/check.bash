#!/usr/bin/env bash
# Refuse GNU-only command options in configuration scripts without a reason.
# - see: #8165
set -euo pipefail

here=$(cd "${BASH_SOURCE[0]%/*}" && pwd)
root=${1:-$(git rev-parse --show-toplevel)}
table=$here/table.json
failed=0
files=0

while IFS=$'\t' read -r tool option expression; do
  while IFS= read -r file; do
    case $file in
      *.bash | *.toml) ;;
      *) continue ;;
    esac
    previous=
    line_number=0
    while IFS= read -r line || [[ -n $line ]]; do
      (( line_number += 1 ))
      if [[ $line =~ $expression ]] \
        && [[ ! $previous =~ ^[[:space:]]*#[[:space:]]gnu-only:[[:space:]]+[^[:space:]].*$ ]]; then
        printf '%s:%s: GNU-only option `%s %s` needs a `# gnu-only: <reason>` line before it\n' \
          "$file" "$line_number" "$tool" "$option" >&2
        failed=1
      fi
      previous=$line
    done < "$root/$file"
    (( files += 1 ))
  done < <(git -C "$root" ls-files -- .config)
done < <(jq -r '.[] | [.tool, .option, .expression] | @tsv' "$table")

(( failed == 0 )) || exit 1
printf 'gnu-options check OK: %s options scan %s configuration scripts\n' "$(jq length "$table")" "$files"
