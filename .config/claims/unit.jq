# Whether an issue is a unit issue work may start on (#2532): one line per
# missing or malformed section, or nothing. `unit:check` prints them.
#
# Input: the issue's body, as a string.
#
# A unit issue carries, each with content (`units.md` § units-issue):
#
# - `## Sources`: items `` - `<key>` — <what it decides> ``, each marked
#   primary or secondary;
# - `## Readings`: a table marking each of the six axes `yes` or `no`;
# - `## Concerns`, `## Ledger` and `## Not in this slice`;
# - `## The shape` and `## Try first`, when the body says it is new
#   territory.
#
# A section's HTML comments are not content, so the issue template's hints
# leave a section unanswered until it is written.

include "sections";

def need($name):
  (section($name) // null) as $lines
  | if $lines == null then "`## \($name)` is missing"
    elif ($lines | filled | not) then "`## \($name)` is empty"
    else empty
    end;

. as $body
| need("Sources"),
  ((section("Sources") // []) as $lines
    | ($lines | items | select(keyed == null) | "`## Sources` line `\(.)` is not `- `<key>` — <what it decides>`"),
      ($lines | items | keyed | select(. != null) | select(.text | test("\\b(primary|secondary)\\b"; "i") | not)
        | "`## Sources` line `\(.line)` marks its source neither primary nor secondary")),
  (if section("Readings") == null then "`## Readings` is missing"
   else [marks] as $marks
   | (axes[] | . as $axis
       | if ([$marks[] | select(.axis == $axis)] | length) == 0 then "`## Readings` has no row for `\($axis)`"
         elif ([$marks[] | select(.axis == $axis and .mark != null)] | length) == 0 then "`## Readings` marks `\($axis)` neither `yes` nor `no`"
         else empty
         end)
   end),
  need("Concerns"),
  need("Ledger"),
  need("Not in this slice"),
  (if $body | gsub("(?s)<!--.*?-->"; "") | test("new territory"; "i") then need("The shape"), need("Try first") else empty end)
