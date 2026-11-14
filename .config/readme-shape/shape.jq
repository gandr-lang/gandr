# The shape of a crate README (#7616): each `crates/*/README.md` holds the
# parts that `crates/README.md` § Crate README shape lists, in that order. The
# input is `{rule, readmes}`: the text of `crates/README.md`, and the lines of
# each README by its path. The output is one line for each README that
# departs, `<path>:<line>: <departure>`, which names its first departure.
#
# The check reads the parts from the rule's list, so the rule has one home:
# each `N. `## <name>`` item gives a part and its place, `, always` after the
# name marks a part that each README holds, and the bold openers in an item
# are the openers that its part holds in order. The title, the lead sentence
# and the table of contents come first in each README. The table lists each
# part that the README holds, in the README's order.

def place: "crates/README.md § Crate README shape";

def section:
  .rule | (capture("\n## Crate README shape\n(?<body>(?:.|\n)*?)(?=\n## |\\z)").body // "");

def parts:
  [section
   | splits("\n")
   | select(test("^[0-9]+\\. `## "))
   | capture("^[0-9]+\\. `## (?<name>[^`]+)`(?<rest>.*)$")
   | {name, always: (.rest | test("^, always")),
      openers: [.rest | scan("\\*\\*([A-Z][a-z]+)\\.\\*\\*") | .[0]]}];

# The parts and the bold openers of a README, outside its code fences.
def events($lines):
  reduce range(0; $lines | length) as $i ({fence: false, out: []};
    $lines[$i] as $line
    | if $line | test("^```") then .fence |= not
      elif .fence then .
      elif $line | startswith("## ") then .out += [{line: ($i + 1), part: $line[3:]}]
      elif $line | test("^\\*\\*[A-Z][a-z]+\\.\\*\\*") then
        .out += [{line: ($i + 1), opener: ($line | capture("^\\*\\*(?<word>[A-Z][a-z]+)").word)}]
      else . end)
  | .out;

def blank: test("^\\s*$") or test("^<!--.*-->$");

# The first line at or after `$from` that is not blank, or null.
def next_line($lines; $from):
  first(range($from; $lines | length) | select($lines[.] | blank | not)) // null;

# The departures of the title, the lead and the table of contents, and the
# table's entries, `{line, name}`.
def head($lines):
  if ($lines[0] // "") | test("^# \\S") | not then {departures: [{line: 1, what: "the first line is not `# <package>`"}], toc: []}
  else next_line($lines; 1) as $lead
  | if $lead == null or ($lines[$lead] | test("^(#|- |\\||<!--)")) then
      {departures: [{line: (($lead // 0) + 1), what: "no sentence after the title"}], toc: []}
    else next_line($lines; $lead + 1) as $start
    | if $start == null or ($lines[$start] | test("^- \\[") | not) then
        {departures: [{line: (($start // $lead) + 1), what: "no table of contents after the lead"}], toc: []}
      else
        {departures: [],
         toc: [first(range($start; $lines | length) | select($lines[.] | test("^(- \\[|\\s+- \\[|<!--.*-->$)") | not)) // ($lines | length)
               | range($start; .)
               | . as $i
               | $lines[$i]
               | select(test("^- \\["))
               | {line: ($i + 1), name: capture("^- \\[(?<name>[^\\]]+)\\]").name}]}
      end
    end
  end;

def departures($lines; $parts):
  ($parts | map(.name)) as $names
  | ($parts | to_entries | map({key: .value.name, value: .key}) | from_entries) as $rank
  | head($lines) as $head
  | events($lines) as $events
  | [$events[] | select(.part)] as $held
  | $head.departures[],
    ($held
     | to_entries[]
     | .key as $k
     | .value as $h
     | if $rank[$h.part] == null then {line: $h.line, what: "`## \($h.part)`: a part that the rule does not name"}
       elif $k > 0 and ($rank[$held[$k - 1].part] // -1) >= $rank[$h.part] then
         {line: $h.line, what: "`## \($h.part)`: out of order, after `## \($held[$k - 1].part)`"}
       else empty end),
    ($parts[]
     | select(.openers != [])
     | . as $part
     | first($held[] | select(.part == $part.name)) as $at
     | ([$held[] | select(.line > $at.line) | .line] | min // infinite) as $end
     | [$events[] | select(.opener and .line > $at.line and .line < $end) | .opener] as $got
     | select($got != $part.openers)
     | {line: $at.line, what: "`## \($part.name)`: the bold openers are \($got | map("**\(.).**") | join(", ") | if . == "" then "none" else . end), where the rule gives \($part.openers | map("**\(.).**") | join(", "))"}),
    (($head.toc | map(.name)) as $toc
     | ($held | map(.part)) as $order
     | select($head.departures == [] and $toc != $order)
     | first(range(0; [$toc, $order] | map(length) | max) | select($toc[.] != $order[.])) as $i
     | {line: ($head.toc[$i].line // $held[$i].line),
        what: "the table of contents lists \($toc[$i] // "nothing" | if . == "nothing" then . else "`\(.)`" end) where the README holds \($order[$i] // "nothing" | if . == "nothing" then . else "`## \(.)`" end)"}),
    ($parts[]
     | select(.always and (.name | IN($held[].part) | not))
     | {line: ($lines | length), what: "`## \(.name)`: absent, and the rule holds it always"});

parts as $parts
| if ($parts | length) == 0 then "\(place) lists no part"
  else .readmes
  | to_entries[]
  | .key as $path
  | first(departures(.value; $parts)) // empty
  | "\($path):\(.line): \(.what)"
  end
