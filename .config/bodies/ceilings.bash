#!/usr/bin/env bash
# The ceilings a change adds (#5039, `units.md` § units-engineering), read
# by `pr:open` and handed to `opening.jq`'s `ceilings`:
#
#   ceilings.bash <base> [head]
#
# Prints a JSON array of `{path, line, kind, text, cites}`, one per ceiling
# that a Rust line the change from <base> to <head>, `HEAD` by default, adds
# opens. A ceiling is a `spec_clause_traversal` waiver, the lint's name
# inside an `expect(` or `allow(` that opens on its line or on one of the
# three lines above it, or an `economy:` comment. Its extent is read from
# the head's file, since its citation can stand on a later line: a waiver
# runs to the line that closes its group, and a comment runs while the next
# line continues it with the same marker and no new `<word>:` head. `kind`
# is `waiver` or `economy`, `text` is the opening line trimmed, and `cites`
# holds each `#<n>` of the extent, in order and once.
#
# A move adds no ceiling (#7126). The ceilings of the reverse change, from
# <head> to <base> with the base's text, are the ceilings that the change
# removes. An added ceiling whose kind and extent, each line trimmed, are
# those of a removed ceiling moves, and the list leaves it out. Each removed
# ceiling matches one added ceiling at most.
set -euo pipefail
base=${1:?usage: ceilings.bash <base> [head]}
head=${2:-HEAD}

# The ceilings that the change from $1 to $2 adds, each with its extent's
# lines trimmed, read from the text of $2.
added() {
  local from=$1 to=$2 file path
  git diff -U0 --no-renames --no-color "$from" "$to" -- ':(glob)**/*.rs' \
    | jq -Rs '[foreach (split("\n")[]) as $line ({path: null, at: 0, hit: null};
        .hit = null
        | if ($line | startswith("+++ ")) then .path = ($line | sub("^\\+\\+\\+ (b/)?"; ""))
          elif ($line | startswith("@@ ")) then .at = ($line | capture("\\+(?<n>[0-9]+)").n | tonumber)
          elif ($line | startswith("+")) then
            (if ($line | test("spec_clause_traversal|economy:")) then .hit = {path, line: .at} else . end) | .at += 1
          else . end;
        .hit // empty)] | group_by(.path) | map({path: .[0].path, lines: map(.line)}) | .[]' -c \
    | while IFS= read -r file; do
        path=$(jq -r .path <<< "$file")
        git show "$to:$path" | jq -Rs --arg path "$path" --slurpfile lines <(jq -c .lines <<< "$file") '
          split("\n") as $text
          | def trimmed: sub("^\\s+"; "") | sub("\\s+$"; "");
            def cites($from; $to): [$text[$from:$to + 1][] | scan("(?<![\\w/&])#([0-9]+)\\b") | .[0] | tonumber]
              | reduce .[] as $n ([]; if index([$n]) then . else . + [$n] end);
            def marker($i): $text[$i] | capture("^\\s*(?<m>//[/!]?)") .m // null;
            def continues($i; $m): ($text[$i] // null) as $next
              | $next != null and marker($i) == $m
              and ($next | sub("^\\s*//[/!]?"; "") | test("^\\s*$") | not)
              and ($next | sub("^\\s*//[/!]?\\s*"; "") | test("^(-\\s+)?`?[a-z][a-z-]*:\\s") | not);
            def comment_end($i): marker($i) as $m | def go($k): if continues($k + 1; $m) then go($k + 1) else $k end; go($i);
            def group_end($i): ([range($i; [$i + 12, ($text | length)] | min) | select($text[.] | test("\\)"))] | first) // $i;
          [$lines[0][] | (. - 1) as $i
            | $text[$i] as $open
            | if ($open | test("spec_clause_traversal"))
                 and any(range([$i - 3, 0] | max; $i + 1); $text[.] | test("\\b(expect|allow)\\("))
              then {kind: "waiver", end: group_end($i)}
              elif ($open | test("//[/!]?.*\\beconomy:")) then {kind: "economy", end: comment_end($i)}
              else empty end
            | {path: $path, line: ($i + 1), kind, text: ($open | trimmed), cites: cites($i; .end),
               extent: [$text[$i:.end + 1][] | trimmed]}]'
      done \
    | jq -s 'add // []'
}

jq -n --slurpfile added <(added "$base" "$head") --slurpfile removed <(added "$head" "$base") '
  reduce $added[0][] as $ceiling ({listed: [], unmatched: $removed[0]};
    ([.unmatched[] | {kind, extent}] | index([$ceiling | {kind, extent}])) as $match
    | if $match == null then .listed += [$ceiling | del(.extent)] else .unmatched |= del(.[$match]) end)
  | .listed'
