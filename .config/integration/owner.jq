# The owner of a red head of `landing` (#6587), read by `landing:watch`.
# The search over the first parents (`search.jq`) names the first commit
# where a check fails. GitHub names the pull request that brings that
# commit, and its branch `<lane>-<n>-…` names the lane. The watcher files
# one defect for each failing check, or updates the open one, claims it for
# that lane, and pages that lane's seat `FIX`.
#
# The input holds `check`, the failing check; `head`, the red head;
# `green`, the last head where the gate passes; `culprit`, the first commit
# where the check fails; `pr`, its pull request `{number, branch, title}`,
# or null when GitHub names none; `lines`, the failing lines of the check's
# log; and `open`, the open defects whose title opens `landing:`, each
# `{number, title}`.
#
# The output holds `lane`, the culprit's lane, or `triage` when no pull
# request names it; `title`, the defect's title; `number`, the open
# defect that matches the check, or null when the watcher files a new one;
# `observation`, the body that a new defect opens with under
# `## Observation`, or the comment on the open one; and `page`, the `FIX`
# line, `{n}` standing for the number
# when the watcher files a new defect.
def short: .[0:9];
. as $in
| ($in.pr // null) as $pr
| (if $pr == null then "triage" else ($pr.branch | split("-")[0]) end) as $lane
| "landing: `\($in.check)` fails" as $prefix
| ([$in.open[] | select(.title | startswith($prefix + " "))] | first // null) as $match
| (if $pr == null then "commit \($in.culprit | short)" else "#\($pr.number) (\($in.culprit | short))" end) as $brings
| {
    lane: $lane,
    title: "\($prefix) from \($brings)",
    number: ($match.number // null),
    observation: (((if $match == null then ["## Observation", ""] else [] end) + [
      "`landing:watch` runs `\($in.check)` on the head `\($in.head | short)` of `landing`, and the check fails. It passes on `\($in.green | short)`, the last green head.",
      "",
      "The search over the first parents names `\($in.culprit | short)` as the first commit where the check fails. \(if $pr == null then "GitHub names no pull request for it, so the claim goes to the fixer." else "Pull request #\($pr.number), \"\($pr.title)\", brings it, so the claim goes to the lane `\($lane)`." end)",
      "",
      "The failing lines:",
      "",
      "```text",
      ($in.lines[]),
      "```"
    ]) | join("\n")),
    page: "FIX #\($match.number // "{n}"): `\($in.check)` fails on landing at \($in.head | short), and \($brings) brings it. Repair it on landing, never with a revert."
  }
