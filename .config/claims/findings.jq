# What a unit issue lacks before work may start on it (#2532): `findings`
# gives one line per missing or malformed section of the body it is applied
# to, or nothing. `unit:check` prints them (`unit.jq`); `claim:next` prints
# them as the pick's sections due (`next.jq`, #3134), and `pr:open` refuses a
# landing on an issue that has any (`signed.jq`).
#
# A unit issue carries, each with content (`units.md` § units-issue):
#
# - `## Sources`: items `` - `<key>` — <what it decides> ``, each marked
#   primary or secondary, or `` - `<key>` — not read: <why> `` for an owner
#   the term map routes to and the unit declines (#3158);
# - `## Readings`: a table answering each of the seven axes `yes — <what it
#   gives this unit>` or `no — <why it does not reach it>`, a reason on both
#   (#2955); a refused row quotes the axis's question;
# - `## Concerns`: a table marking each concern of `ledger/concerns.sql`
#   `yes` or `no` (#2795);
# - `## Ledger` and `## Not in this slice`;
# - `## After`: `none`, or one `- #n — <what it waits for>` per issue the
#   unit waits on (#2902). The section is the record; `unit:check` sets each
#   one as the issue's GitHub `blocked by` dependency, and a dependency stated
#   in prose, a line `after: …`, is refused;
# - `## The shape` and `## Try first`, when the body says it is new
#   territory.
#
# A section's HTML comments are not content, so a hint left in a section
# leaves it unanswered until it is written. The unit form
# (`.github/ISSUE_TEMPLATE/unit.yml`, #3113) writes its fields as these
# sections through the issues workflow.

include "sections";

def need($name):
  (section($name) // null) as $lines
  | if $lines == null then "`## \($name)` is missing"
    elif ($lines | filled | not) then "`## \($name)` is empty"
    else empty
    end;

def findings:
  . as $body
  | need("Sources"),
    ((section("Sources") // []) as $lines
      | ($lines | items | select(keyed == null) | "`## Sources` line `\(.)` is not `- `<key>` — <what it decides>`"),
        ($lines | items | keyed | select(. != null) | select(.text | test("\\b(primary|secondary)\\b|^\\s*not read:\\s*\\S"; "i") | not)
          | "`## Sources` line `\(.line)` marks its source neither primary nor secondary")),
    (if section("Readings") == null then "`## Readings` is missing"
     else [marks] as $marks
     | (axes[] | . as $axis
         | [$marks[] | select(.axis == $axis)] as $rows
         | if ($rows | length) == 0 then "`## Readings` has no row for `\($axis)`; the axis asks \(questions[$axis])"
           elif ([$rows[] | select(.mark != null)] | length) == 0 then "`## Readings` marks `\($axis)` neither `yes` nor `no`; the axis asks \(questions[$axis])"
           elif ([$rows[] | select(.mark != null and .reason != null)] | length) == 0 then
             "`## Readings` marks `\($axis)` `\(first($rows[] | select(.mark != null)).mark)` without a reason: write `yes — <what it gives this unit>` or `no — <why it does not reach it>`; the axis asks \(questions[$axis])"
           else empty
           end)
     end),
    (if section("Concerns") == null then "`## Concerns` is missing"
     else [concern_marks] as $marks
     | (concerns[] | . as $concern
         | if ([$marks[] | select(.concern == $concern)] | length) == 0 then "`## Concerns` has no row for `\($concern)`"
           elif ([$marks[] | select(.concern == $concern and .mark != null)] | length) == 0 then "`## Concerns` marks `\($concern)` neither `yes` nor `no`"
           else empty
           end)
     end),
    need("Ledger"),
    need("Not in this slice"),
    (after as $after
     | "`none`, or one `- #n — <what it waits for>` per issue the unit waits on" as $form
     | if $after == null then "`## After` is missing: write \($form)"
       elif $after.empty then "`## After` is empty: write \($form)"
       else ($after.malformed[] | "`## After` line `\(.)` is not \($form)"),
         (if $after.none and ($after.numbers | length) > 0 then "`## After` says `none` and lists issues: keep the issues, or `none` alone" else empty end)
       end),
    ($body | lines[] | select(test("^after:\\s"; "i"))
      | "the line `\(.)` states a dependency in prose: list each issue in `## After` as `- #n — <what it waits for>`, and `unit:check --fix` sets it on GitHub"),
    (if $body | gsub("(?s)<!--.*?-->"; "") | test("new territory"; "i") then need("The shape"), need("Try first") else empty end);
