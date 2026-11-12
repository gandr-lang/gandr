# The body of the scaling account of `gandr check` (#6879), which
# `bench:scaling` writes with each row it measures.
#
# Input: {body, row, widths, placement, paths, share, limit, closed}.
# - `body`: the open account's body, or null when there is none.
# - `row`: the measured head, {head, date, load, points, placement, hotpath,
#   defect}. `points` are `curve.jq`'s, `placement` is {median}, `hotpath` is
#   [{wall}] in the order of `widths`, and `defect` is the number of the
#   defect that the row's fall opened, or null.
# - `widths` and `placement`: the points of the host's configuration, each
#   {threads, nodes}. `paths`: the roots that `gandr check` reads.
# - `share`: the fall of the widest speed-up that opens a defect, as a
#   fraction. `limit`: the most characters that the body holds.
# - `closed`: the defects of earlier falls that are closed now.
#
# Output: {body, moved, fall}.
# - `body` holds the prose, then a table with one row for each measured head,
#   the newest first. A row of the head of `row` already in the body is
#   replaced, so a pass run again writes the same body.
# - `moved` is null, or the table of the oldest rows that leave the body
#   once it passes `limit`, which the task posts as one comment. The body
#   then keeps three quarters of `limit` at most.
# - `fall` is null, or the fields of the defect when `row` is `idle` and its
#   widest speed-up is lower by `share` or more than that of the newest
#   `idle` row before it. Its `table` holds the header and the two rows, for
#   the defect's observation.
# A row's verdict reads `accepted`, `fall: #<n>` while its defect is open,
# and `fixed: #<n>` once that defect closes. The collector reading
# (`.config/claims/sections.jq`) settles every row but an open fall.

def two: (. * 100 | round) as $c | "\($c / 100 | floor).\($c % 100 | tostring | if length == 1 then "0" + . else . end)";
def short: .[0:9];
def cells: sub("^\\|"; "") | sub("\\|$"; "") | [splits("\\|")] | map(gsub("^\\s+|\\s+$"; ""));

. as $in
| ($in.widths | length) as $n
| "| Head | Date | Host | \($in.widths | map("\(.threads) on \(.nodes)") | join(" | ")) | \($in.placement.threads) on \($in.placement.nodes) | Hotpath at \($in.widths | map(.threads | tostring) | join(", ")) | Verdict |" as $header
| "| --- | --- | --- | \([range($n)] | map("--:") | join(" | ")) | --: | --: | --- |" as $rule
| ([($in.body // "") | split("\n")[] | select(test("^\\| `[0-9a-f]{9}` \\|"))]
    | map(. as $line | cells as $c
      | {line: $line, head: ($c[0] | gsub("`"; "")), load: $c[2],
         widest: ($c[2 + $n] | capture(", (?<s>[0-9.]+)×") // null | if . == null then null else .s | tonumber end)})
    | map(select(.head != ($in.row.head | short)))) as $before
| ($in.row.points | last | .speedup) as $now
| ([$before[] | select(.load == "idle" and .widest != null)] | first) as $previous
| (if $in.row.load == "idle" and $previous != null and $previous.widest > 0
      and (($previous.widest - $now) / $previous.widest) >= $in.share
   then {head: ($in.row.head | short), previous: $previous.head, before: ($previous.widest | two), now: ($now | two),
         drop: ((($previous.widest - $now) / $previous.widest * 100) | round | tostring),
         share: ($in.share * 100 | round | tostring), threads: ($in.widths | last | .threads | tostring),
         nodes: ($in.widths | last | .nodes)}
   else null end) as $fall
| (if $fall == null then "accepted" elif $in.row.defect == null then "fall" else "fall: #\($in.row.defect)" end) as $verdict
| ("| `\($in.row.head | short)` | \($in.row.date) | \($in.row.load) | "
   + ([range($n) as $i | $in.row.points[$i] | if $i == 0 then "\(.median | two) s" else "\(.median | two) s, \(.speedup | two)×" end] | join(" | "))
   + " | \($in.row.placement.median | two) s | \($in.row.hotpath | map(.wall | two) | join(" · ")) s | \($verdict) |") as $line
| (if $fall == null then null else $fall + {table: ([$header, $rule, $line, $previous.line] | join("\n"))} end) as $fall
| [$line] + [$before[] | .line
    | (capture("\\| fall: #(?<n>[0-9]+) \\|$") // null) as $f
    | if $f != null and ($in.closed | index($f.n | tonumber)) != null then sub("\\| fall: #(?<n>[0-9]+) \\|$"; "| fixed: #\(.n) |") else . end] as $rows
| ([
    "This issue is the scaling account of `gandr check` on the wide host (#6879). `mise run bench:scaling` adds one row for each head of `main` that it measures, the newest first.",
    "",
    "- A cell of the curve gives the median wall time of three runs of `gandr check --recheck \($in.paths | join(" "))`, and the speed-up against one thread. Its column names the threads and the NUMA nodes of the point.",
    "- The placement column gives the median of three runs at \($in.placement.threads) threads on the nodes that it names. Compare it with the cell of the same width on fewer nodes.",
    "- The hotpath column gives the wall time of one run of the `gandr` hotpath series at each width of the curve, on the same nodes.",
    "- The host reads `held` while a mutation run holds the wide host. The account never compares such a row.",
    "- A row whose speed-up at \($in.widths | last | .threads) threads is \($in.share * 100 | round) % or more below that of the newest `idle` row before it is a fall. A fall opens a defect, and its row reads `fixed` once the defect closes.",
    "",
    $header,
    $rule
  ] | join("\n")) as $prose
| def body($kept): $prose + "\n" + ($kept | join("\n")) + "\n";
  if (body($rows) | length) <= $in.limit then {body: body($rows), moved: null, fall: $fall}
  else
    (reduce range($rows | length; 0; -1) as $k (null;
       if . == null and (body($rows[0:$k]) | length) <= ($in.limit * 3 / 4) then $k else . end)) as $keep
    | ($keep // 1) as $keep
    | {body: body($rows[0:$keep]),
       moved: (["The account moves these rows out of its body, the newest first.", "", $header, $rule] + $rows[$keep:] | join("\n")) + "\n",
       fall: $fall}
  end
