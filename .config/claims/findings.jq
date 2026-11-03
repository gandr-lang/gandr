# What a unit issue lacks before work may start on it (#2532): `findings`
# gives one line per missing or malformed section of the body it is applied
# to, or nothing; its argument is the issue's labels, read by the sections
# only some kinds of unit carry. `unit:check` prints them (`unit.jq`);
# `claim:next` prints them as the pick's sections due (`next.jq`, #3134), and
# `pr:open` refuses a landing on an issue that has any (`signed.jq`).
#
# A unit issue carries, each with content (`units.md` § units-issue):
#
# - `## Sources`: a table with the columns Source, Role and What it gives
#   (#3594), one row per source. The Source cell names the source in
#   backquotes. The Role is `primary`, `secondary`, `oracle` for the system a
#   shallow embedding is compared with (#3964), or `not read` for an owner
#   the term map routes to and the unit declines (#3158). A `not read` row
#   gives its reason in What it gives. A list item is refused;
# - `## Embedding owes`, on a unit with an `oracle` row (#3964): one
#   `- #n — <the operation>` per operation the oracle has and gandr lacks,
#   each its own issue, or `none — <why nothing is owed>`;
# - `## Readings`: a table answering each of the eight axes `yes — <what it
#   gives this unit>` or `no — <why it does not reach it>`, a reason on both
#   (#2955); a refused row quotes the axis's question;
# - `## Concerns`: a table marking each concern of `ledger/concerns.sql`
#   `yes` or `no` (#2795);
# - `## Ledger` and `## Not in this slice`;
# - `## After`: `none`, or one `- #n — <what it waits for>` per issue the
#   unit waits on (#2902). The section is the record; `unit:check` sets each
#   one as the issue's GitHub `blocked by` dependency, and a dependency stated
#   in prose, a line `after: …`, is refused;
# - `## Surface`, on a `kind:feature` labelled `area:surface` or `area:theory`
#   (#4637; a `std` feature carries `area:surface`): its first line is
#   `tier <0–4> — <why the tier below does not read well enough>`, or
#   `none — <why the feature has no surface>`. The tiers are the owner's
#   scale: 0 names and combinators, 1 a user notation, 2 a reader
#   `#name{ … }`, 3 an attribute `@[…]`, 4 a clause position bound to a `std`
#   interface;
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

# Whether the labels ask for `## Surface` (#4637). An issue the coordinator
# signed is never judged for it again, so no unit signed before the rule, or
# in flight, becomes unclaimable.
def surfaced($labels):
  ($labels | index("kind:feature")) != null and ($labels | index("shape:signed")) == null
  and any($labels[]; . == "area:surface" or . == "area:theory");

def surface($labels):
  if surfaced($labels) | not then empty
  else
    "`tier <0–4> — <why the tier below does not read well enough>`, or `none — <why the feature has no surface>` (`units.md` § units-issue)" as $form
    | (section("Surface") // null) as $lines
    | if $lines == null then "`## Surface` is missing: a feature in `area:surface` or `area:theory` states the tier it proposes, \($form)"
      elif ($lines | filled | not) then "`## Surface` is empty: write \($form)"
      else ($lines | join("\n") | gsub("(?s)<!--.*?-->"; "") | split("\n") | map(select(test("\\S"))) | first | sub("^[-*]\\s+"; "")) as $first
      | if $first | test("^(tier [0-4]|none) —\\s*\\S") then empty
        else "`## Surface` opens `\($first)`, not \($form)"
        end
      end
  end;

def findings($labels):
  . as $body
  | need("Sources"),
    ((section("Sources") // []) as $lines
      | [source_rows] as $rows
      | ($lines | items | "`## Sources` line `\(.)` is a list item: write it as a row of the table `| Source | Role | What it gives |`"),
        (if ($rows | length) == 0 and ([$lines | items] | length) == 0 and ($lines | filled)
         then "`## Sources` holds no table: write `| Source | Role | What it gives |` and one row per source" else empty end),
        ($rows[]
          | if (.keys | length) == 0 then "`## Sources` row `\(.line)` names no source in backquotes"
            elif IN(.role; source_roles[]) | not then "`## Sources` row `\(.line)` gives the role `\(.role)`: write `primary`, `secondary`, `oracle` or `not read`"
            elif .role == "not read" and .text == "" then "`## Sources` row `\(.line)` declines its source with no reason in What it gives"
            else empty
            end)),
    (if any(source_rows; .role == "oracle") then
       owes as $owes
       | "one `- #n — <the operation>` per operation the oracle has and gandr lacks, each its own issue, or `none — <why nothing is owed>`" as $form
       | if $owes == null then "`## Embedding owes` is missing: the unit names an `oracle` in `## Sources`, so write \($form)"
         elif $owes.empty then "`## Embedding owes` is empty: write \($form)"
         else ($owes.malformed[] | "`## Embedding owes` line `\(.)` is not \($form)"),
           (if $owes.none and ($owes.numbers | length) > 0 then "`## Embedding owes` says `none` and lists issues: keep the issues, or `none` and its reason alone" else empty end)
         end
     else empty end),
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
    (if $body | gsub("(?s)<!--.*?-->"; "") | test("new territory"; "i") then need("The shape"), need("Try first") else empty end),
    surface($labels);
