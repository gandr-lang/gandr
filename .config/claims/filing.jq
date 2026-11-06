# What a merged pull request's `## Refactoring` verdict files (#2885), as
# `refactor:file` carries it out. A `yes` or a `maybe` with at least one row
# joins the one open refactor collector of the unit's area, so a verdict does
# not open an issue of its own. The follow-up then does not depend on the
# lane that opened the pull request, which has moved on, and the board grows
# by at most one issue for each area.
#
# Input: an object with
#   pr      {number, body, area}: the merged pull request, and the area of
#           the unit it closed, or null when none is read;
#   issues  every `kind:refactor` issue, open or closed, as {number, state,
#           title, body}.
# Output: one decision, as compact JSON:
#   {act: "none"}                  the verdict is `no`, absent, or names no row;
#   {act: "filed", issue}          an issue already carries `from: #<pr>`, so
#                                  a second watch or the stall detector's
#                                  retry files nothing;
#   {act: "update", issue, body}   the area's collector is open: it gains the
#                                  rows it lacks and one more `from:` line;
#   {act: "open", title, body, labels}
#                                  the area has no open collector: the title
#                                  `refactor(<area>): verdicts`, the body the
#                                  sentence that says what it is (#3596), then
#                                  the table under `## Observation` and a
#                                  one-sentence lead, and `from: #<pr>`, the
#                                  labels `kind:refactor`, `collector` and
#                                  `area:<area>` (no `area:` when none is
#                                  read; `issue:file` then refuses it, and
#                                  the stall detector pages the
#                                  coordinator).

include "sections";

def collector_title($area): "refactor(\($area // "unplaced")): verdicts";
def opening($area):
  if $area == null then "This issue collects the refactoring verdicts of the merged pull requests whose unit names no area."
  else "This issue collects the refactoring verdicts of the merged pull requests in the `\($area)` area." end;
def lead: "The table gives each row that a verdict names.";

. as $in
| ($in.pr.body | refactoring) as $r
| def table: "| Kind | Where | Observation |\n| --- | --- | --- |\n" + (map(.line) | join("\n"));
  if $r == null or ($r.verdict | IN("yes", "maybe") | not) or $r.rows == [] then {act: "none"}
  else
    first($in.issues[] | select(.body | from_lines | any(.[]; . == $in.pr.number)) | {act: "filed", issue: .number})
    // (collector_title($in.pr.area) as $title
    | ([$in.issues[] | select(.state == "OPEN" and .title == $title)] | min_by(.number)) as $collector
    | if $collector != null then
        ([($collector.body | section("Observation") // [] | refactor_rows)[].line]) as $observed
        | ([$r.rows[] | select(.line | IN($observed[]) | not)]) as $new
        | ($collector.body | split("\n")) as $lines
        | ([range(0; $lines | length) | select($lines[.] | test("^\\s*\\|"))] | last) as $end
        | {act: "update", issue: $collector.number,
           body: ((if $new == [] then $lines
                   elif $end == null then ["## Observation", "", lead, "", ($new | table), ""] + $lines
                   else $lines[:$end + 1] + [$new[].line] + $lines[$end + 1:] end)
                  | join("\n") | sub("\n*$"; "") + "\nfrom: #\($in.pr.number)\n")}
      else
        {act: "open",
         title: $title,
         body: "\(opening($in.pr.area))\n\n## Observation\n\n\(lead)\n\n\($r.rows | table)\n\nfrom: #\($in.pr.number)\n",
         labels: (["kind:refactor", "collector"] + (if $in.pr.area == null then [] else ["area:\($in.pr.area)"] end))}
      end)
  end
