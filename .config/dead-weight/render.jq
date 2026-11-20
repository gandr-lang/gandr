# The report's one issue and each crate's items (#2891), the last stage of
# `report:dead-weight`. Input: {items, dates, today, grace, repository,
# commit, lonely}: `items` as `verdicts.jq` gives them; `dates` the date of
# each item's lines, by "<file>:<start>-<end>", as `blame.jq` gives them;
# `today` and the grace in days; the repository `OWNER/NAME` and the commit
# the records describe; `lonely` the crates that no other crate names, each
# with the epics its README's `## References` names. Output: {title, count,
# areas, body, crates}: the title of the one issue, its count of rows, the
# area labels of its crates, and its body, a table with one row for each
# crate: the crate, the count of its rows and the age of its oldest row in
# days. `crates` holds one {crate, count, body} for each crate with an item
# past the grace, sorted by crate, the body the tables of its items that
# `--crate` prints. An item with no date, or with a date in the grace, is
# left out.
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
  | if ["boot", "core", "kernel", "runtime", "storage", "surface", "theory", "workflow"] | index($word) then $word
    else "workflow" end;

# The table of the rows `$rows` under the heading `$heading` and its lead.
def table($heading; $lead; $rows):
  ["## \($heading)", $lead,
   (["| Item | Visibility | Callers | Since |", "| --- | --- | --- | --- |"]
    + ($rows | map("| \(.cell) | \(if .exported then "`pub`" else "not exported" end) | \(.callers) | \(.since) |"))
    | join("\n"))]
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
    | {crate: $crate,
       count: (if $lonely[$crate] != null then 1 else length end),
       oldest: (map(days(.since; $in.today)) | max),
       body: ([
         "The items of `\($crate)` that no code outside tests names, and its exported items that no other crate names, at `\($in.commit[:9])` (#2891).",
         (if $lonely[$crate] != null then
            "## No consumer yet\n\nNo other crate names `\($crate)`, so each of its \(length) items waits for its consumer, and no row asks for one item.\n\n| Crate | Items | Answer |\n| --- | --- | --- |\n| `\($crate)` | \(length) | waits for \(if ($lonely[$crate] | length) > 0 then $lonely[$crate] | map("#\(.)") | join(", ") else "the epic that its README names; the README names none yet" end) |"
          else
            (if ($unused | length) > 0 then
               table("No caller outside tests"; "The table gives each item that only tests name, or that nothing names. The answer is `find the consumer`: a test, a corpus exemplar or the crate that takes the item. A deletion is the last answer, with the architect's sign-off."; $unused)
             else empty end),
            (if ($local | length) > 0 then
               table("Exported with no use in another crate"; "The table gives each exported item that only its own crate names. The answer is `find the consumer`: the crate that takes the item, or a narrower visibility once the design names none."; $local)
             else empty end)
          end)
       ] | join("\n\n"))})
| {title: "refactor: dead weight",
   count: (map(.count) | add // 0),
   areas: (map(.crate | "area:\(area_of)") | unique),
   body: ([
     "This issue lists each crate that holds items that no code outside tests names, or exported items that no other crate names (#2891).",
     "`mise run report:dead-weight` writes the table each night from the compiler's records of `\($in.commit[:9])`. It leaves out an item that a commit touched in the last \($in.grace) days, and each item in `.config/dead-weight/kept.txt`. `mise run report:dead-weight --crate <dir>` prints the items of one crate. A unit that takes an item out cites this issue, and its `## Deletes` row needs the architect's sign-off (#6817). An item that a decision keeps goes into the kept list with its decision.",
     "## Crates",
     "The table gives each crate, the count of its rows and the age of its oldest row in days. The answer for each item is `find the consumer`.",
     (["| Crate | Rows | Oldest |", "| --- | --- | --- |"] + map("| `\(.crate)` | \(.count) | \(.oldest) |") | join("\n"))
   ] | join("\n\n")),
   crates: map({crate, count, body})}
