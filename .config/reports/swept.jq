# What the night's recovery sweep does to the open recovery collectors
# (#3326, #3732): the guard keeps each one's rows, and the collector closes
# itself on the first night its cause is gone.
#
# Input:
#   causes   the report's causes: [{name, kind, families: [name]}], kind
#            `deleted` or `missed`
#   issues   the open `collector` issues titled `recovery: <name> marks other
#            bytes than a <kind> tile`: [{number, title, body}]
#
# Output: one {number, body, close} per collector whose body changes or which
# closes. Each family row, `- [ ] `<family>``, is ticked when the night's
# cause of the collector's name and kind no longer lists the family, and
# unticked when it lists it again. A night whose report has no such cause
# ticks every row and closes the collector (`close`): the sweep reads every
# exemplar each night, so a cause it does not report is gone.

include "sections";

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
| ($before
    | lines
    | map((row // null) as $row
        | if $row == null then .
          else "\($row.lead)[\(if ($tonight | index($row.family | family)) then " " else "x" end)]\($row.rest)"
          end)
    | join("\n")) as $after
| select($after != $before or ($present | not))
| {number, body: $after, close: ($present | not)}
