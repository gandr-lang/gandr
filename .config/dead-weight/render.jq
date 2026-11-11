# The issue body of each crate (#2891), the last stage of
# `report:dead-weight`. Input: {items, dates, today, grace, budget,
# repository, commit, lonely}: `items` as `verdicts.jq` gives them; `dates`
# the date of each item's lines, by "<file>:<start>-<end>", as `blame.jq`
# gives them; `today` and the grace in days; the most characters the rows of
# one table take, or null for no bound; the repository `OWNER/NAME` and the
# commit the records describe; `lonely` the crates that no other crate names,
# each with the epics its README's `## References` names. Output: one {crate,
# area, title, count, body} for each crate with an item past the grace,
# sorted by crate. An item with no date, or with a date in the grace, is left
# out. A table past the budget gives the number of rows that it leaves out.
# GitHub refuses a body past 65,536 characters, so two tables at 28,000 each
# fit with their text.
#
# A row asks for the consumer of its item, and never for its deletion
# (#6817): 27 deletions by the rows' `delete` took items that open units need.
# A crate that no other crate names gets one row for the crate, which waits
# for the epics its README names, and no row for each item.

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
| ($in.lonely // {}) as $lonely
| [ .items[]
    | . + {since: ($in.dates["\(.file):\(.start)-\(.end)"] // null)}
    | select(.since != null and days(.since; $in.today) >= $in.grace)
    | . + {cell: "[`\(.path)`](https://github.com/\($in.repository)/blob/\($in.commit)/\(.file)#L\(.line))"} ]
| group_by(.crate)
| map(.[0].crate as $crate
    | map(select(.verdict == "unused")) as $unused
    | map(select(.verdict == "local")) as $local
    | {crate: $crate, area: ($crate | area_of), title: "refactor(\($crate)): dead weight",
       count: (if $lonely[$crate] != null then 1 else length end),
       body: ([
         "This issue lists the items of `\($crate)` that no code outside tests names, and its exported items that no other crate names (#2891).",
         "`mise run report:dead-weight` writes the tables each night from the compiler's records of `\($in.commit[:9])`. It leaves out an item that a commit touched in the last \($in.grace) days, and each item in `.config/dead-weight/kept.txt`. A unit that takes an item out cites this issue, and its `## Deletes` row needs the architect's sign-off (#6817). An item that a decision keeps goes into the kept list with its decision.",
         (if $lonely[$crate] != null then
            "## No consumer yet\n\nNo other crate names `\($crate)`, so each of its \(length) items waits for its consumer, and no row asks for one item.\n\n| Crate | Items | Answer |\n| --- | --- | --- |\n| `\($crate)` | \(length) | waits for \(if ($lonely[$crate] | length) > 0 then $lonely[$crate] | map("#\(.)") | join(", ") else "the epic that its README names; the README names none yet" end) |"
          else
            (if ($unused | length) > 0 then
               table("No caller outside tests"; "The table gives each item that only tests name, or that nothing names. The answer is `find the consumer`: a test, a corpus exemplar or the crate that takes the item. A deletion is the last answer, with the architect's sign-off."; $unused; $in.budget; $crate)
             else empty end),
            (if ($local | length) > 0 then
               table("Exported with no use in another crate"; "The table gives each exported item that only its own crate names. The answer is `find the consumer`: the crate that takes the item, or a narrower visibility once the design names none."; $local; $in.budget; $crate)
             else empty end)
          end)
       ] | join("\n\n"))})
