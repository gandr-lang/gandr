# The issue body of each crate (#2891), the last stage of
# `report:dead-weight`. Input: {items, dates, today, grace, budget,
# repository, commit}: `items` as `verdicts.jq` gives them; `dates` the date
# of each item's lines, by "<file>:<start>-<end>", as `blame.jq` gives them;
# `today` and the grace in days; the most characters the rows of one table
# take, or null for no bound; the repository `OWNER/NAME` and the commit the
# records describe. Output: one {crate, area, title, count, body} for each
# crate with an item past the grace, sorted by crate. An item with no date,
# or with a date in the grace, is left out. A table past the budget gives the
# number of rows that it leaves out. GitHub refuses a body past 65,536
# characters, so two tables at 28,000 each fit with their text.

# The days from the date `$since` to the date `$until`, both YYYY-MM-DD.
def days($since; $until):
  (($until | strptime("%Y-%m-%d") | mktime) - ($since | strptime("%Y-%m-%d") | mktime)) / 86400;

# The area of a crate: the first word of its directory, which names an
# area, or `workflow` for a file outside `crates/`.
def area_of:
  split("-")[0] as $word
  | if ["core", "kernel", "runtime", "storage", "surface", "theory", "workflow"] | index($word) then $word
    else "workflow" end;

# The table of the rows `$rows` under the heading `$heading` and its lead,
# with the rows that fit in `$budget` characters; `$crate` names the crate
# for the line that counts the rows left out.
def table($heading; $lead; $rows; $budget; $crate):
  ($rows | map("| \(.cell) | \(if .exported then "`pub`" else "not exported" end) | \(.callers) | \(.since) |")) as $lines
  | ([foreach $lines[] as $line (0; . + ($line | length) + 1; .)
     | select($budget == null or . <= $budget)] | length) as $shown
  | (($lines | length) - $shown) as $left
  | ["## \($heading)", $lead,
     (["| Item | Visibility | Callers | Since |", "| --- | --- | --- | --- |"] + $lines[:$shown] | join("\n")),
     (if $left > 0 then
        "The table leaves out \($left) more \(if $left == 1 then "row" else "rows" end). `mise run report:dead-weight --crate \($crate)` prints them all."
      else empty end)]
  | join("\n\n");

. as $in
| [ .items[]
    | . + {since: ($in.dates["\(.file):\(.start)-\(.end)"] // null)}
    | select(.since != null and days(.since; $in.today) >= $in.grace)
    | . + {cell: "[`\(.path)`](https://github.com/\($in.repository)/blob/\($in.commit)/\(.file)#L\(.line))"} ]
| group_by(.crate)
| map(.[0].crate as $crate
    | map(select(.verdict == "unused")) as $unused
    | map(select(.verdict == "local")) as $local
    | {crate: $crate, area: ($crate | area_of), title: "refactor(\($crate)): dead weight", count: length,
       body: ([
         "This issue lists the items of `\($crate)` that no code outside tests names, and its exported items that no other crate names (#2891).",
         "`mise run report:dead-weight` writes the tables each night from the compiler's records of `\($in.commit[:9])`. It leaves out an item that a commit touched in the last \($in.grace) days, and each item in `.config/dead-weight/kept.txt`. A unit that deletes or narrows an item cites this issue. An item that a decision keeps goes into the kept list with its decision.",
         (if ($unused | length) > 0 then
            table("No caller outside tests"; "The table gives each item that only tests name, or that nothing names. The refactoring is `delete`."; $unused; $in.budget; $crate)
          else empty end),
         (if ($local | length) > 0 then
            table("Exported with no use in another crate"; "The table gives each exported item that only its own crate names. The refactoring is `consolidate`: narrow the item's visibility."; $local; $in.budget; $crate)
          else empty end)
       ] | join("\n\n"))})
