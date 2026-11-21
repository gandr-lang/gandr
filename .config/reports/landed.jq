# What a merged pull request does to the collectors it advances (#3732). A
# body that works a `collector` says `Advances #n` and lists the rows it
# clears under `## Rows` (#3326, `opening.jq`). On the merge each listed row,
# `- [ ] `<row>``, is ticked, and a collector left with no open row
# (`collector_rows`) closes, its comment naming the landing.
#
# Two landings that advance one collector and merge at once read the same
# body, and the later write would drop the ticks of the earlier (#5583). So a
# merge ticks the rows of every merged landing that advances the collector:
# the merged body's, and those of each body in `landings`. A tick is the same
# whoever writes it, so the last write holds the ticks of both.
#
# Input:
#   body     the merged pull request's body
#   issues   the issues the body advances: [{number, labels, body, landings}],
#            `landings` the bodies of the merged pull requests on the issue's
#            timeline, none when it is absent
#
# Output: one {number, body, close} per `collector` the body advances whose
# body changes or which closes. A table row is the guard's to settle, so only
# a checkbox row is ticked, and a collector with an open table row stays open.

include "sections";
include "targets";

def row: capture("^(?<lead>\\s*[-*] )\\[ \\](?<rest>\\s*(?<text>.*))$");
def table_key:
  if test("^\\s*\\|") and (test("^\\s*\\|(\\s*:?-+:?\\s*\\|)+\\s*$") | not)
  then sub("^\\s*\\|\\s*"; "") | [splits("(?<!\\\\)\\|")][0] | gsub("\\\\\\|"; "|") | row_key
  else null end;

def open_table_key:
  table_key as $key
  | if $key != null and (test("(?<!\\\\)\\|\\s*(landed|fixed|accepted|runner shift)\\b"; "i") | not)
    then $key
    else null
    end;

def marked($named):
  lines
  | reduce .[] as $line (
      {shape: false, lines: []};
      (if $line | test("^## ") then .shape = ($line | test("^## (Sources|Readings|Concerns|Engineering|Settled)\\s*(:.*)?$")) else . end)
      | .shape as $shape
      | ($line | row // null) as $row
      | ($line | open_table_key) as $table
      | .lines += [
          if $row != null and ($named | index($row.text | row_key)) then "\($row.lead)[x]\($row.rest)"
          elif ($shape | not) and $table != null and ($named | index($table)) then ($line | sub("\\s*\\|\\s*$"; " | landed |"))
          else $line
          end
        ])
  | .lines | join("\n");


# The keys of the rows a landing's body clears in the collector `$n`: none
# when the body does not advance `$n`.
def named($n):
  if targets("advances") | index($n) then
    [section("Rows") // [] | items | sub("^[-*]\\s+"; "") | row_key]
  else [] end;

.body as $merged
| ($merged | targets("advances")) as $advanced
| .issues[]
| select(.number as $n | ((.labels // []) | index("collector")) and ($advanced | index($n)))
| .number as $n
| ([$merged] + (.landings // []) | map(named($n)) | add) as $named
| (.body // "") as $before
| ($before | marked($named)) as $after
| ($after | collector_rows | length == 0) as $close
| select($after != $before or $close)
| {number, body: $after, close: $close}
