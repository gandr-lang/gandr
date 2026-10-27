# What a merged pull request's `## Refactoring` verdict files (#2885), as
# `refactor:file` carries it out: a `yes` or a `maybe` with at least one row
# becomes a `kind:refactor` issue, so the follow-up does not depend on the
# lane that opened the pull request, which has moved on.
#
# Input: an object with
#   pr      {number, body, area}: the merged pull request, and the area of
#           the unit it closed, or null when none is read;
#   issues  every `kind:refactor` issue, open or closed, as {number, state,
#           body}.
# Output: one decision, as compact JSON:
#   {act: "none"}                  the verdict is `no`, absent, or names no row;
#   {act: "filed", issue}          an issue already carries `from: #<pr>`, so
#                                  a second watch or the stall detector's
#                                  retry files nothing;
#   {act: "update", issue, body}   a `maybe` one of whose `Where`s an open
#                                  `kind:refactor` issue's `## Observation`
#                                  names: that issue gains the rows it lacks
#                                  and one more `from:` line;
#   {act: "open", title, body, labels}
#                                  the new issue: the title
#                                  `refactor(<area>): <first Kind> — <its
#                                  Where>`, the body the table verbatim under
#                                  `## Observation` and `from: #<pr>`, the
#                                  labels `kind:refactor`, `area:<area>` and
#                                  `status:unsectioned` (no `area:` when none
#                                  is read; `issue:file` then refuses it, and
#                                  the stall detector pages the coordinator).

include "sections";

. as $in
| ($in.pr.body | refactoring) as $r
| def table: "| Kind | Where | Observation |\n| --- | --- | --- |\n" + (map(.line) | join("\n"));
  def whereas: [.[].whereas[]] | unique;
  if $r == null or ($r.verdict | IN("yes", "maybe") | not) or $r.rows == [] then {act: "none"}
  else
    first($in.issues[] | select(.body | from_lines | any(.[]; . == $in.pr.number)) | {act: "filed", issue: .number})
    // (($r.rows | whereas) as $whereas
    | (if $r.verdict == "maybe" then
         [first($in.issues[] | select(.state == "OPEN")
           | (.body | section("Observation") // [] | refactor_rows) as $observed
           | select(any(($observed | whereas)[]; IN($whereas[])))
           | {issue: .number, body, observed: [$observed[].line]})][0]
       else null end) as $match
    | if $match != null then
        ([$r.rows[] | select(.line | IN($match.observed[]) | not)]) as $new
        | ($match.body | split("\n")) as $lines
        | ([range(0; $lines | length) | select($lines[.] | test("^\\s*\\|"))] | last) as $end
        | {act: "update", issue: $match.issue,
           body: ((if $end == null or $new == [] then $lines
                   else $lines[:$end + 1] + [$new[].line] + $lines[$end + 1:] end)
                  | join("\n") | sub("\n*$"; "") + "\nfrom: #\($in.pr.number)\n")}
      else
        {act: "open",
         title: "refactor(\($in.pr.area // "unplaced")): \($r.rows[0].kind) — \($r.rows[0].whereas | join(", "))",
         body: "## Observation\n\n\($r.rows | table)\n\nfrom: #\($in.pr.number)\n",
         labels: (["kind:refactor"] + (if $in.pr.area == null then [] else ["area:\($in.pr.area)"] end) + ["status:unsectioned"])}
      end)
  end
