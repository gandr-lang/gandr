# What a merged pull request's `## Refactoring` verdict files (#2885), as
# `refactor:file` carries it out. A `yes` or a `maybe` with at least one row
# joins the one open refactor collector of the tree, so a verdict does not
# open an issue of its own. The follow-up then does not depend on the lane
# that opened the pull request, which has moved on, and the board holds one
# collector. Under its `## Observation`, the rows of each area stand under a
# `### <area>` heading, `### unplaced` for a unit that names no area.
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
#   {act: "update", issue, body, labels}
#                                  the collector is open: the heading of the
#                                  area gains the rows the collector lacks,
#                                  the body one more `from:` line, and the
#                                  issue the label `area:<area>`;
#   {act: "open", title, body, labels}
#                                  no collector is open: the title
#                                  `refactor: verdicts`, the body the sentence
#                                  that says what it is (#3596), then under
#                                  `## Observation` a one-sentence lead, the
#                                  heading of the area and its table, and
#                                  `from: #<pr>`, the labels `kind:refactor`,
#                                  `collector` and `area:<area>` (no `area:`
#                                  when none is read; `issue:file` then
#                                  refuses it, and the stall detector pages
#                                  the coordinator).

include "sections";

def collector_title: "refactor: verdicts";
def opening: "This issue collects the refactoring verdicts of the merged pull requests. The rows of each area stand under the heading of the area.";
def lead: "The table of each area gives each row that a verdict names.";
def heading($area): "### \($area // "unplaced")";
def area_labels($area): if $area == null then [] else ["area:\($area)"] end;

. as $in
| ($in.pr.body | refactoring) as $r
| def table: "| Kind | Where | Observation |\n| --- | --- | --- |\n" + (map(.line) | join("\n"));
  if $r == null or ($r.verdict | IN("yes", "maybe") | not) or $r.rows == [] then {act: "none"}
  else
    first($in.issues[] | select(.body | from_lines | any(.[]; . == $in.pr.number)) | {act: "filed", issue: .number})
    // (([$in.issues[] | select(.state == "OPEN" and .title == collector_title)] | min_by(.number)) as $collector
    | if $collector != null then
        ([($collector.body | section("Observation") // [] | refactor_rows)[].line]) as $observed
        | ([$r.rows[] | select(.line | IN($observed[]) | not)]) as $new
        | ($collector.body | split("\n")) as $lines
        | ([range(0; $lines | length) | select($lines[.] == heading($in.pr.area))] | first) as $start
        | ([range(0; $lines | length) | select($lines[.] | test("^from: #"))] | first // ($lines | length)) as $from
        # The last table line under the area's heading, before the next
        # heading or the `from:` lines.
        | (if $start == null then null
           else ([range($start + 1; $lines | length) | select($lines[.] | test("^#|^from: #"))] | first // ($lines | length)) as $stop
           | [range($start + 1; $stop) | select($lines[.] | test("^\\s*\\|"))] | last
           end) as $end
        | {act: "update", issue: $collector.number,
           body: ((if $new == [] then $lines
                   elif $end != null then $lines[:$end + 1] + [$new[].line] + $lines[$end + 1:]
                   elif $start != null then $lines[:$start + 1] + ["", ($new | table)] + $lines[$start + 1:]
                   else $lines[:$from]
                     + (if $lines | index("## Observation") then [] else ["## Observation", "", lead, ""] end)
                     + [heading($in.pr.area), "", ($new | table), ""] + $lines[$from:]
                   end)
                  | join("\n") | sub("\n*$"; "") + "\nfrom: #\($in.pr.number)\n"),
           labels: area_labels($in.pr.area)}
      else
        {act: "open",
         title: collector_title,
         body: "\(opening)\n\n## Observation\n\n\(lead)\n\n\(heading($in.pr.area))\n\n\($r.rows | table)\n\nfrom: #\($in.pr.number)\n",
         labels: (["kind:refactor", "collector"] + area_labels($in.pr.area))}
      end)
  end
