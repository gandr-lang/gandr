# The design work that no open issue holds (#3401, #3160 step 6): one line
# for each design page and each open unit of a unit table that no open issue
# names, or nothing.
#
# Input:
#   absorption  the vault's page statuses as `report:absorption` writes them,
#               `{"<filename>": [{path, status}]}`, or null where no vault
#               checkout has written them, as in CI
#   pages       the vault pages that hold a unit table: [{name, text}], name
#               the page's filename; null or absent where no vault checkout
#               is configured
#   issues      the open issues: [{number, body}]; an issue whose `state` is
#               not open, in any case, holds nothing
#
# A page whose status is `design`, where no `## Sources` row of an open issue
# names its filename, prints `design page <filename>: no open unit names it`.
# A row key names the page by its filename or by a path that ends in it.
#
# A table is a unit table when its header holds a `complete` column and each
# of its rows holds a box there, `[ ]` or `[x]`. The first cell of a row is
# its unit number, and a row whose box is empty is an open unit. An open issue
# cites a unit when its body names the page's filename and writes `unit <n>`,
# or `units` before a list or a range that holds `<n>`: `units 51, 53 and
# 58`, `units 16 to 22`. Each open unit that no open issue cites prints
# `design page <filename> unit <n>: no open unit names it`. A table with no
# `complete` column, or with a row that holds no box, is no unit table.

include "sections";

# The cells of a table line, trimmed. A cell ends at an unescaped `|`.
def cells: sub("^\\s*\\|"; "") | sub("(?<!\\\\)\\|\\s*$"; "") | [splits("(?<!\\\\)\\|")] | map(gsub("^\\s+|\\s+$"; ""));
def table_line: test("^\\s*\\|");
def rule_line: table_line and (cells | all(test("^:?-+:?$")));

# Each unit table of a page's text, as [{unit, open}], in row order.
def unit_tables:
  split("\n") as $lines
  | range(0; ($lines | length) - 1) as $i
  | select(($lines[$i] | table_line) and ($lines[$i + 1] | rule_line))
  | ($lines[$i] | cells | map(ascii_downcase) | index("complete")) as $box
  | select($box != null)
  | $lines[$i + 2:] as $after
  | ([range(0; $after | length) | select($after[.] | table_line | not)] | first // ($after | length)) as $end
  | [$after[:$end][] | cells | {unit: .[0], box: (.[$box] // "")}]
  | select(length > 0 and all(.box | test("^\\[[ xX]\\]$")))
  | map({unit, open: (.box == "[ ]")});

# The unit numbers a body cites: each `unit <n>`, and each number of a list
# or a range after `units`.
def cited:
  [match("(?i)\\bunits?\\s+([0-9]+(?:(?:\\s*,\\s*(?:and\\s+)?|\\s+and\\s+|\\s+to\\s+|\\s*[-–]\\s*)[0-9]+)*)"; "g")
    | .captures[0].string
    | [splits("\\s*,\\s*(?:and\\s+)?|\\s+and\\s+")]
    | .[]
    | if test("^[0-9]+(\\s+to\\s+|\\s*[-–]\\s*)[0-9]+$")
      then [scan("[0-9]+") | tonumber] as [$from, $to] | range($from; $to + 1) | tostring
      else . end]
  | unique;

[(.issues // [])[] | select((.state // "open") | ascii_downcase == "open")] as $issues
| ([$issues[] | .body // "" | source_rows | .keys[] | split("/") | last] | unique) as $sourced
| [(.absorption // {}) | to_entries | sort_by(.key)[]
    | select(any(.value[]; .status == "design"))
    | .key
    | select(IN($sourced[]) | not)
    | "design page \(.): no open unit names it"] as $pages
| [(.pages // [])[] | .name as $name
    | ([$issues[] | .body // "" | select(contains($name)) | cited[]] | unique) as $named
    | .text | unit_tables | .[]
    | select(.open and (.unit | IN($named[]) | not))
    | "design page \($name) unit \(.unit): no open unit names it"] as $units
| $pages + $units
| join("\n")
