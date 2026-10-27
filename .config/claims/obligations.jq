# How the obligations are answered (#2886): `report:obligations`'s rule, over
# merged pull requests and the unit issues they close. Each table has the lane
# (the unit's `area:`, `none` for a pull request closing no area-labelled
# issue) as its row and the ISO week of the merge as its column:
# - Concerns: of the unit issue's `## Concerns` rows, how many are marked `no`.
# - Sources read: the pull request's items by disposition (`taken`,
#   `departed`, `declined`, `read`, `n/a`, `deferred`, anything else
#   `other`), and how many `taken:` name a site (a backquoted span).
# - Readings: the axes the unit issue selects `yes`, and how many the pull
#   request's `## Readings` row answers naming a site.
# - Refactoring: the pull request's verdicts, `absent` where it has none.
# - Ledger: the rows its `## Ledger` names (items with a backquoted id).
# No figure is judged: the coordinator reads the report.
#
# Input: {since, until, prs: [{number, merged, lane, body, issue}]},
# `merged` an ISO 8601 time, `issue` the unit's body or null.
# Output: the issue body, a string.

include "sections";

def week: strptime("%Y-%m-%dT%H:%M:%SZ") | mktime | strftime("%G-W%V");
def sited: test("`");
def dispositions: ["taken", "departed", "declined", "read", "n/a", "deferred", "other"];

# One pull request's answers.
def fact:
  .body as $body
  | .issue as $issue
  | {lane, week: (.merged | week),
     concerns: (if $issue == null then [] else [$issue | concern_marks | .mark] end),
     sources: [$body | (section("Sources read") // []) | items | keyed | select(. != null) | .text
       | (capture("^(?<d>taken|departed|declined|read|n/a|deferred):\\s*(?<rest>.*)$") // {d: "other", rest: .})
       | {d, sited: (.d == "taken" and (.rest | sited))}],
     readings: (if $issue == null then []
       else [$body | (section("Readings") // []) | lead | rows] as $rows
       | [$issue | marks | select(.mark == "yes") | .axis]
       | map(. as $axis | {axis: $axis, sited: any($rows[]; (.cells | index($axis)) != null and (.cells[-1] | test("^answered\\b") and sited))})
       end),
     refactoring: ($body | refactoring | if . == null then "absent" else (.verdict // "unread") end),
     ledger: [$body | (section("Ledger") // []) | items | keyed | select(. != null)] | length};

def count(f): map(select(f)) | length;

# The cells of each table, from the facts of one lane and week.
def concerns_cell: [.[].concerns[]] | if length == 0 then "—" else "\(count(. == "no")) of \(length) no" end;
def sources_cell:
  [.[].sources[]] as $all
  | if ($all | length) == 0 then "—"
    else [dispositions[] as $d
      | ($all | count(.d == $d)) as $n
      | select($n > 0)
      | if $d == "taken" then "taken \($n) (\($all | count(.sited)) at a site)" else "\($d) \($n)" end]
    | join(" · ")
    end;
def readings_cell: [.[].readings[]] | if length == 0 then "—" else "\(length) selected, \(count(.sited)) answered at a site" end;
def refactoring_cell:
  [.[].refactoring] as $all
  | [("yes", "maybe", "no", "unread", "absent") as $v | ($all | count(. == $v)) as $n | select($n > 0) | "\($v) \($n)"]
  | join(" · ");
def counted($n; $word): "\($n) \($word)\(if $n == 1 then "" else "s" end)";
def ledger_cell: "\(counted(map(.ledger) | add; "row")), \(counted(length; "pull request"))";

def table($heading; $intro; cell):
  . as $facts
  | ([.[].week] | unique) as $weeks
  | ([.[].lane] | unique) as $lanes
  | "### \($heading)\n\n\($intro)\n\n| Lane | \($weeks | join(" | ")) |\n| --- |\($weeks | map(" --- |") | join(""))\n"
    + ([$lanes[] as $lane
        | "| \($lane) | \([$weeks[] as $week | $facts | map(select(.lane == $lane and .week == $week)) | if length == 0 then "" else cell end] | join(" | ")) |"]
       | join("\n"));

[.prs[] | fact] as $facts
| [
    "Obligation answers on the pull requests merged from \(.since) to \(.until), by lane (the unit's `area:`) and ISO week of the merge (#2886): \($facts | length) pull requests, \($facts | count((.concerns | length) > 0)) with a sectioned unit issue. Written each night by `mise run report:obligations`; no figure here is a gate.",
    if ($facts | length) == 0 then "No pull request merged in the period."
    else
      ($facts | table("Concerns answered `no`"; "The unit issue's `## Concerns` rows marked `no`, of all its rows."; concerns_cell)),
      ($facts | table("Sources read, by disposition"; "The pull request's `## Sources read` items by disposition; a `taken:` at a site names it in backquotes."; sources_cell)),
      ($facts | table("Readings selected"; "The axes the unit issue selects `yes`, and those the pull request's `## Readings` answers naming a site."; readings_cell)),
      ($facts | table("Refactoring verdicts"; "The pull request's `## Refactoring` verdict; `absent` where it has none."; refactoring_cell)),
      ($facts | table("Ledger rows moved"; "The rows the pull request's `## Ledger` names."; ledger_cell))
    end
  ] | join("\n\n") + "\n"
