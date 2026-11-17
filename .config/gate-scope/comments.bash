#!/usr/bin/env bash
# Prints each `.rs` path whose change against <base> touches `//` comment
# lines alone, one per line (#6648). `select.bash` maps such a path to the
# table's `comments` groups: a `//` comment compiles to no item and no
# documentation, so its change runs no `check:doc` and no `check:corpus`.
#
# A changed line is a comment when, past its indentation, it opens on `//`
# and on neither `///` nor `//!`. A blank line, a block comment, code before
# a comment, and a doc comment read as code. A path added, deleted or
# untracked reads as code too. A `//` line inside a string literal reads as
# a comment: the gate still runs Clippy and the package's tests on it.
#
# Each `git diff` is read into a variable, so its failure stops the script
# and never reads as a change of comments alone.
#
# Usage: comments.bash <base> [<head>]
set -euo pipefail
base=$1
head=${2:-}
range=("$base")
if [[ -n $head ]]; then range+=("$head"); fi
comment='^[[:space:]]*//($|[^/!]|//)'
paths=$(git diff --no-renames --name-only --diff-filter=M "${range[@]}" -- '*.rs')
[[ -n $paths ]] || exit 0
while IFS= read -r path; do
  diff=$(git diff --no-renames --no-color --no-ext-diff -U0 "${range[@]}" -- "$path")
  only=true
  hunk=false
  while IFS= read -r line; do
    case $line in
      '@@ '*) hunk=true ;;
      'diff --git '*) hunk=false ;;
      '\'*) ;;
      [+-]*)
        if [[ $hunk == true && ! ${line:1} =~ $comment ]]; then
          only=false
          break
        fi
        ;;
      *)
        if [[ $hunk == true ]]; then
          only=false
          break
        fi
        ;;
    esac
  done <<< "$diff"
  if [[ $only == true ]]; then printf '%s\n' "$path"; fi
done <<< "$paths"
