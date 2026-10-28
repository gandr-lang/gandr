# The nightly tracker report (#2902): what an open issue says it waits on
# that GitHub does not record, and each open issue short of its label set, as
# {count, body}, the body the one issue `report: dependencies` carries.
#
# Input:
#   issues    the open issues that state a dependency, and the epics:
#             [{number, labels: [name], body, blocked_by: [number],
#             sub_issues: [{number, state}]}], blocked_by every issue GitHub
#             has it blocked by, sub_issues an epic's (others: [])
#   open      every open issue: [{number, labels: [name]}]
#   owing     the features ledger's rows resting on issues as owing work
#             (`.config/ledger/owing.bash`): [{row, issues: [number]}]
#   defaults  `.config/issues/defaults.toml` as JSON
#   previous  the report issue's body as the last night left it, or ""
#
# Five findings, each keyed `<kind>:<issue>:<blocker>` (`labels:<issue>`,
# `ledger:<row>`):
#
# - prose: a line outside `## After` naming an open issue as `after #n`,
#   `blocked on #n`, `waits on #n`, `once #n lands` or `needs #n`, with no
#   dependency on it set; never in a `collector`'s body, a guard's record of
#   other issues, whose phrases this report's own table quotes (#3347);
# - after: an issue `## After` lists with no dependency on it set;
# - epic: an epic's open sub-issue the epic is not blocked by;
# - labels: an issue short of its label set, one `kind:`, `priority:` and
#   `effort:` and one or more `area:` (`labelled` in
#   `.config/issues/labels.jq`), what `issue:labels --sweep` repairs
#   included: a kind's default, a `kind:` beside `kind:epic`;
# - ledger: a ledger row none of whose owing issues is open, which
#   `check:ledger` refuses, or whose open ones are all epics, each of which
#   closes itself once the issues it is blocked by close (#3398), so that
#   its closing would turn `check:ledger` red.
#
# The body keeps each finding's count of nights running in a trailing
# comment; one at three nights or more is named a refusal candidate, the
# step the issue states for a finding that recurs.

include "sections";
include "labels";

def phrases: "(?i)\\b(?:after|blocked on|waits on|needs) #(?<n>[0-9]+)\\b|\\bonce #(?<m>[0-9]+) lands\\b";

# The body's lines outside its `## After` section.
def outside_after:
  lines as $lines
  | ([range(0; $lines | length) | select($lines[.] | test("^## After\\s*$"))] | first) as $start
  | if $start == null then $lines
    else ([range($start + 1; $lines | length) | select($lines[.] | test("^## "))] | first // ($lines | length)) as $end
    | $lines[:$start] + $lines[$end:]
    end;

def nights_cell: "\(.nights)\(if .nights >= 3 then " — a refusal candidate" else "" end)";

. as $root
| [.open[].number] as $open
| .defaults as $defaults
| ((.previous // "") | capture("<!-- deps-report: (?<counts>\\{.*?\\}) -->").counts // "{}" | fromjson) as $nights
| [.issues[]
    | .number as $self
    | (.blocked_by // []) as $set
    | def unset($n): $n != $self and ($open | index($n)) != null and ($set | index($n)) == null;
    ((select((.labels // []) | index("collector") | not)
        | .body // "" | outside_after[]
        | match(phrases; "g")
        | {n: ((.captures | map(select(.string != null)) | first.string) | tonumber), phrase: .string}
        | select(unset(.n))
        | {key: "prose:\($self):\(.n)", issue: $self, blocker: .n, found: "says `\(.phrase)`"}),
     ((.body // "" | after // {numbers: []}).numbers[]
        | select(. as $n | unset($n))
        | {key: "after:\($self):\(.)", issue: $self, blocker: ., found: "`## After` lists it"}),
     (if (.labels // []) | index("kind:epic") then
        (.sub_issues // [])[] | select(.state == "open" and unset(.number))
        | {key: "epic:\($self):\(.number)", issue: $self, blocker: .number, found: "an open sub-issue"}
      else empty end))]
| unique_by(.key)
| sort_by(.issue, .blocker)
| map(. + {nights: (($nights[.key] // 0) + 1)}) as $deps
| [$root.open[]
    | .number as $self
    | [{labels, defaults: $defaults} | labelled
        | split("\t")
        | if .[0] == "add" then "no `\(.[1] | sub(":.*"; ":"))` (its kind's default: `\(.[1])`)"
          elif .[0] == "remove" then "`\(.[1])` beside `kind:epic`"
          else .[1] end]
    | select(length > 0)
    | {key: "labels:\($self)", issue: $self, found: join("; ")}]
| sort_by(.issue)
| map(. + {nights: (($nights[.key] // 0) + 1)}) as $labels
| ($root.open | map({(.number | tostring): .labels}) | add // {}) as $labelled
| [($root.owing // [])[]
    | .row as $row
    | [.issues[] | select($labelled[tostring])] as $live
    | if ($live | length) == 0 then
        {key: "ledger:\($row)", row: $row, found: "owes on \(.issues | map("#\(.)") | join(", ") | if . == "" then "no issue" else "\(.), no open issue" end): `check:ledger` refuses it; name the open issue that owes the rest"}
      elif ($live | all($labelled[tostring] | index("kind:epic"))) then
        {key: "ledger:\($row)", row: $row, found: "owes on \($live | map("#\(.)") | join(", ")), an epic that closes itself once the issues it is blocked by close: `check:ledger` turns red then unless the row names an open unit first"}
      else empty end]
| sort_by(.row)
| map(. + {nights: (($nights[.key] // 0) + 1)}) as $ledger
| ($deps + $labels + $ledger) as $all
| {count: ($all | length),
   body: (if ($all | length) == 0 then
      "This report finds nothing for the tracker to repair (`mise run report:deps`, #2902). GitHub records every dependency an open issue states. Every open issue carries its full label set. Every ledger row owes on an open issue.\n"
    else
      "This report lists what the tracker must repair (`mise run report:deps`, #2902). It names each dependency an open issue states and GitHub lacks. It names each open issue short of its label set. It names each ledger row that owes on a closed or closing issue. A finding three nights running is a candidate for a refusal.\n"
      + (if ($deps | length) > 0 then
          "\n## Dependencies\n\nThe table lists each dependency an issue states and GitHub does not record. To repair a `## After` or a line of prose, list the issue in `## After` and run `mise run unit:check --fix <n>`. To repair an epic, run `mise run epic:deps <n>`.\n\n| Issue | Waits on | Found | Nights |\n| --- | --- | --- | --- |\n"
          + ($deps | map("| #\(.issue) | #\(.blocker) | \(.found) | \(nights_cell) |") | join("\n")) + "\n"
        else "" end)
      + (if ($labels | length) > 0 then
          "\n## Labels\n\nThe table lists each open issue short of its label set. An issue carries one `kind:`, one `priority:`, one `effort:` and one or more `area:`. An epic carries `kind:epic` alone. `mise run issue:labels --sweep` repairs a default and an epic's extra kind. Repair the rest by hand.\n\n| Issue | Found | Nights |\n| --- | --- | --- |\n"
          + ($labels | map("| #\(.issue) | \(.found) | \(nights_cell) |") | join("\n")) + "\n"
        else "" end)
      + (if ($ledger | length) > 0 then
          "\n## Ledger\n\nThe table lists each features row that owes on a closed or closing issue. A row without a witness owes on an open issue (`check:ledger`, #2526, #2635). To repair a row, name the issue that owes the rest in the row's `issue` field. Or name it in the exemplar's `/// Not implemented:` line. Repair the row before the issue closes (#2973).\n\n| Row | Found | Nights |\n| --- | --- | --- |\n"
          + ($ledger | map("| `\(.row)` | \(.found) | \(nights_cell) |") | join("\n")) + "\n"
        else "" end)
      + "\n<!-- deps-report: \($all | map({(.key): .nights}) | add | tojson) -->\n"
    end)}
