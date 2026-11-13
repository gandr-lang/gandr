# The night's chain report (#6893): each architecture's row from
# `chain.jq` beside the last night's row of the same architecture. A chain
# that grows past the share in one night adds an open row to the build's one
# chain collector, with the unit on the chain that grew most. A landing that
# shortens the chain again clears the row under `## Rows`. Two nights compare
# only on one machine: a hosted runner of another processor moves every
# unit's time, so a row whose machine differs from the last night's files
# nothing. A growth already held for its architecture and head adds nothing,
# so a night read twice files once.
#
# Each architecture's part ends with the inputs of the metric of a split
# (#6893, accepted on 2026-11-12), one row for each crate of the workspace
# on the chain: its time, its front end, its edits in a week and the most
# that a split of it can take off the chain.
#
# Input:
#   share   the growth in percent past which a row opens
#   run     {id, url}: the night's run, or null when nothing files
#   rows    tonight's rows, each `chain.jq`'s row with `arch`, `head` and
#           `machine`, the runner's processor and width
#   last    the last night's rows, the same shape; empty when none
#   issues  the open issues of the collector's title: [{number, title, body}]
#   edits   the landings in a week of each source on a chain, by its
#           directory: `git log --since 4.weeks` divided by 4
# Output: {summary, grew, action}. `summary` is the Markdown of the report.
#   `grew` lists each growth as {arch, head, previous, now, before, change,
#   unit, unit_now, unit_before}. `action` is the collector to open (`number`
#   null) or to update, as {number, title, body}, or null.

def hundredths: . * 100 | round / 100;
def seconds: "\(hundredths) s";
def short: .[:9];
def signed: if . > 0 then "+\(hundredths)" else "\(hundredths)" end;

. as $in
| ($in.last | map({key: .arch, value: .}) | from_entries) as $before
| [$in.rows[]
    | . as $row
    | $before[$row.arch] as $last
    | select($last != null and $last.machine == $row.machine)
    | (($row.length - $last.length) / $last.length * 100) as $change
    | select($change > $in.share)
    | ($row.chain | map({unit, now: .seconds, before: ($last.times[.unit] // 0)}) | max_by(.now - .before)) as $unit
    | {arch: $row.arch, head: $row.head, previous: $last.head, now: $row.length, before: $last.length,
       change: ($change | hundredths), unit: $unit.unit, unit_now: $unit.now, unit_before: $unit.before}]
  as $grew
| "perf: the build's chain grows past \($in.share) % in one night" as $title
| ($in.issues | map(select(.title == $title)) | first) as $issue
| ([($issue.body // "") | split("\n")[] | select(test("^- \\[[ x]\\] `"))]) as $held
| [$grew[]
    | . as $g
    | select($held | any(startswith("- [ ] `\($g.arch) \($g.head | short)`") or startswith("- [x] `\($g.arch) \($g.head | short)`")) | not)
    | "- [ ] `\(.arch) \(.head | short)` — the chain takes \(.now | seconds) against \(.before | seconds) at `\(.previous | short)`, \(.change | signed) %; `\(.unit)` takes \(.unit_now | seconds) against \(.unit_before | seconds) ([run \($in.run.id)](\($in.run.url)))"]
  as $new
| {summary: ("## The chain of each head\n\n"
    + "|Architecture|Head|Wall|Units' time|In flight|Chain|Pipelined|Last night|Change|\n"
    + "|---|---|---:|---:|---:|---:|---:|---:|---:|\n"
    + ([$in.rows[]
        | $before[.arch] as $last
        | "|\(.arch)|`\(.head | short)`|\(.wall | seconds)|\(.time | seconds)|\(.in_flight)|\(.length | seconds)|\(.pipelined | seconds)|"
          + (if $last == null then "none|none|"
             elif $last.machine != .machine then "\($last.length | seconds) at `\($last.head | short)`|another machine|"
             else "\($last.length | seconds) at `\($last.head | short)`|\((.length - $last.length) / $last.length * 100 | signed) %|" end)]
       | join("\n"))
    + "\n"
    + ([$in.rows[]
        | "\n### \(.arch) at `\(.head | short)`\n\n"
          + "The build runs \(.units) units on \(.machine). The longest unit is `\(.longest.unit)` at \(.longest.seconds | seconds).\n\n"
          + "<details><summary>The chain: \(.chain | length) units, \(.length | seconds), \(.pipelined | seconds) under pipelining</summary>\n\n"
          + "|Unit|Time|The next unit waits on|\n|---|---:|---|\n"
          + (.chain | map("|`\(.unit)`|\(.seconds | seconds)|\(if .waits == "metadata" then "its metadata" elif .waits == "whole" then "the whole unit" else "none" end)|") | join("\n"))
          + "\n\n</details>\n\n"
          + (if (.off | length) == 0 then "No unit stands off the chain.\n"
             else "|The longest units off the chain|Time|Slack|\n|---|---:|---:|\n"
               + (.off | map("|`\(.unit)`|\(.seconds | seconds)|\(.slack | seconds)|") | join("\n")) + "\n" end)
          + "\n"
          + ([.chain[] | select(.source != null)] as $crates
             | if ($crates | length) == 0 then "No crate of the workspace stands on the chain.\n"
               else "|The crates of the chain|Time|Front end|Edits a week|At most off the chain|\n|---|---:|---:|---:|---:|\n"
                 + ($crates | map("|`\(.unit)`|\(.seconds | seconds)|\(if .front == null then "none" else .front | seconds end)|\(($in.edits // {})[.source] // 0)|\(.bound | seconds)|") | join("\n"))
                 + "\n" end)]
       | join(""))
    + (if ($grew | length) == 0 then "\nNo chain grows past \($in.share) % over the last night.\n"
       else "\n" + ($grew | map("The chain of \(.arch) grows \(.change | signed) % over the last night. `\(.unit)` grows the most: \(.unit_now | seconds) against \(.unit_before | seconds).") | join("\n")) + "\n" end)),
   grew: $grew,
   action: (if $in.run == null or ($new | length) == 0 then null
     else {number: ($issue.number // null),
       title: $title,
       body: ("The nightly reads the chain of each architecture's cold build of the driver against the last night's (#6893). "
         + "A chain that grows past \($in.share) % in one night adds a row here, with the unit on the chain that grows the most. "
         + "A landing that shortens the chain again clears its row under `## Rows`, and the collector closes once no row is open.\n\n"
         + "## Nights\n\n"
         + ($held + $new | join("\n")) + "\n")}
     end)}
