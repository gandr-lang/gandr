#!/usr/bin/env bash
# The lines a change adds where a defect's regression can be named (#2524,
# #3538), read by `pr:open` and handed to `opening.jq`'s `regression`:
#
#   regressions.bash <base>
#
# Prints a JSON array of `{path, text}`, one per line the change from <base>
# to HEAD adds that holds `#` or `_` before a digit, the lines that can name an
# issue alone. The files read are every kind `regression` reads: a corpus
# source, a Rust file, a `.config` JSON case file, a `.config` `cases.bash`
# (#4863) and an extension's TypeScript.
set -euo pipefail
git diff -U0 --no-renames --no-color "$1" HEAD -- \
  ':(glob)corpus/**/*.gandr' ':(glob)**/*.rs' ':(glob).config/**/*.json' ':(glob).config/**/*cases.bash' ':(glob)contrib/**/*.ts' \
  | jq -Rs '[foreach (split("\n")[]) as $line ({path: null};
      if ($line | startswith("+++ ")) then {path: ($line | sub("^\\+\\+\\+ (b/)?"; ""))}
      else {path, text: (if ($line | startswith("+")) then $line[1:] else null end)} end;
      select(.text != null and (.text | test("[#_][0-9]"))))]'
