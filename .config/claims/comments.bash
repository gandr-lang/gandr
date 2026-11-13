#!/usr/bin/env bash
# The comment lines a change removes and does not add back (#6004), read by
# `pr:open` and handed to `opening.jq`'s `facts_kept`:
#
#   comments.bash <base> [<head>]
#
# Prints a JSON array of `{path, removed, dropped}`, one per source under
# `corpus/`, `library/` or `crates/` whose comment lines (`//`, `///`, `//!`)
# the change from <base> to <head>, `HEAD` by default, removes. A removed line
# reads under the path that held it, the `---` path, so a deleted file names
# itself (#7084). It is dropped unless a line the change adds in any file
# carries its trimmed text, so a comment that moves with its code is kept, and
# a reworded one is dropped.
set -euo pipefail
git diff -U0 --no-renames --no-color "$1" "${2:-HEAD}" -- \
  ':(glob)corpus/**/*.gandr' ':(glob)library/**/*.gandr' ':(glob)crates/**/*.rs' \
  | jq -Rs '
      def trimmed: sub("^\\s+"; "") | sub("\\s+$"; "");
      [foreach (split("\n")[]) as $line ({path: null};
          if ($line | startswith("--- ")) then {path: ($line | sub("^--- (a/)?"; "")), skip: true}
          elif ($line | startswith("+++ ")) then {path: .path, skip: true}
          else {path, removed: (if ($line | test("^-\\s*//")) then $line[1:] | trimmed else null end),
                added: (if ($line | startswith("+")) then $line[1:] | trimmed else null end)} end)]
      | (reduce (.[] | .added // empty) as $text ({}; .[$text] += 1)) as $added
      | reduce (.[] | select(.removed != null)) as $row ({added: $added, sources: {}};
          .sources[$row.path].removed += 1
          | if (.added[$row.removed] // 0) > 0 then .added[$row.removed] -= 1
            else .sources[$row.path].dropped += 1 end)
      | .sources | to_entries | map({path: .key, removed: .value.removed, dropped: (.value.dropped // 0)})'
