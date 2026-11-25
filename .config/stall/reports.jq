# The stall reports whose event is over (#3112). `stall:watch` files a
# finding no lane places as a report titled `stall: <kind> on #<n>, whose
# lane `<lane>` no seat holds`; each reading closes every open report whose
# stall no finding of the reading carries any more, so a report never waits
# on a hand to close it. The closing comment names what cleared it: the pull
# request merged or closed unmerged, the refactoring verdict of a merged one
# filed (`verdict-unfiled`, whose pull request is merged from the start), or
# the stall itself cleared.
#
# Input: `{reports, states, findings}`:
#   reports   the open stall reports, `[{number, title}]`; a title of
#             another shape is no report and is left alone;
#   states    each report's pull request's state by its number, `OPEN`,
#             `MERGED` or `CLOSED`; a pull request absent here was not read,
#             and its report is left for the next reading;
#   findings  the reading's findings, `detect.jq`'s `{kind, number, ...}`.
# Output: the reports to close, `[{number, comment}]`, by report number.

. as $in
| [$in.reports[]
    | (.title | capture("^stall: (?<kind>\\S+) on #(?<pr>[0-9]+),")) as $report
    | $in.states[$report.pr] as $state
    | select($state != null)
    | select(any($in.findings[]; .number == ($report.pr | tonumber) and .kind == $report.kind) | not)
    | {number,
       comment: ("Closed by `stall:watch` (#3112): "
         + (if $report.kind == "verdict-unfiled" then "#\($report.pr)'s refactoring verdict is filed"
            elif $state == "MERGED" then "#\($report.pr) merged"
            elif $state == "CLOSED" then "#\($report.pr) closed unmerged"
            else "no reading finds the `\($report.kind)` stall on #\($report.pr) any more"
            end)
         + "; the event this report observed is over.")}]
| sort_by(.number)
