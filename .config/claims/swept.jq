# What the night's recovery sweep does to the open recovery collectors
# (#3326): the guard keeps each one's rows, so a landing that names them
# under `## Rows` sees them closed by the next run, and the collector closes
# itself once its cause stays gone.
#
# Input:
#   causes   the report's causes: [{name, kind, families: [name]}], kind
#            `deleted` or `missed`
#   issues   the open `collector` issues titled `recovery: <name> marks other
#            bytes than a <kind> tile`: [{number, title, body}]
#
# Output: one {number, body, clear, close} per collector whose body changes
# or which closes. Each family row, `- [ ] `<family>``, is ticked when the
# night's cause of the collector's name and kind no longer lists the family,
# and unticked when it lists it again. A night whose report has no such
# cause is a clear run, counted on the body's `<!-- swept: clear <n> -->`
# line; a night that has it takes the line off. The third clear run in a row
# closes the collector (`close`), its rows all ticked.

include "sections";

def marker: "<!-- swept: clear ";
def runs: [lines[] | capture("^<!-- swept: clear (?<n>[0-9]+) -->$") | .n | tonumber] | first // 0;
def row: capture("^(?<lead>\\s*[-*] )\\[(?<mark>[ xX])\\](?<rest> `(?<family>[^`]+)`.*)$");
# A family as the sweep names it: the report spells `command-substitution`
# where older bodies spell `command_substitution`.
def family: gsub("_"; "-");

.causes as $causes
| .issues[]
| (.title | capture("^recovery: (?<name>.+) marks other bytes than a (?<kind>deleted|missed) tile$")) as $cause
| ([$causes[] | select(.name == $cause.name and .kind == $cause.kind) | .families[] | family]) as $tonight
| any($causes[]; .name == $cause.name and .kind == $cause.kind) as $present
| (.body // "") as $before
| (if $present then 0 else ($before | runs) + 1 end) as $clear
| ($before
    | lines
    | map(select(startswith(marker) | not)
        | (row // null) as $row
        | if $row == null then .
          else "\($row.lead)[\(if ($tonight | index($row.family | family)) then " " else "x" end)]\($row.rest)"
          end)
    | (if $clear > 0 then (if .[-1] == "" then .[:-1] else . end) + ["\(marker)\($clear) -->", ""] else . end)
    | join("\n")) as $after
| select($after != $before or $clear >= 3)
| {number, body: $after, clear: $clear, close: ($clear >= 3)}
