# What a merged pull request does to the collectors it advances (#3732). A
# body that works a `collector` says `Advances #n` and lists the rows it
# clears under `## Rows` (#3326, `opening.jq`). On the merge each listed row,
# `- [ ] `<row>``, is ticked, and a collector left with no open row
# (`collector_rows`) closes, its comment naming the landing.
#
# Input:
#   body     the merged pull request's body
#   issues   the issues the body advances: [{number, labels, body}]
#
# Output: one {number, body, close} per `collector` the body advances whose
# body changes or which closes. A table row is the guard's to settle, so only
# a checkbox row is ticked, and a collector with an open table row stays open.

include "sections";
include "targets";

def row: capture("^(?<lead>\\s*[-*] )\\[ \\](?<rest>\\s*(?<text>.*))$");

(.body | targets("advances")) as $advanced
| [(.body | section("Rows") // []) | items | sub("^[-*]\\s+"; "") | row_key] as $named
| .issues[]
| select(.number as $n | ((.labels // []) | index("collector")) and ($advanced | index($n)))
| (.body // "") as $before
| ($before
    | lines
    | map((row // null) as $row
        | if $row != null and ($named | index($row.text | row_key)) then "\($row.lead)[x]\($row.rest)" else . end)
    | join("\n")) as $after
| ($after | collector_rows | length == 0) as $close
| select($after != $before or $close)
| {number, body: $after, close: $close}
