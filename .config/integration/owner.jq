# The owner of a red head of `landing` (#6587), read by `landing:watch`.
# The search over the first parents (`search.jq`) names the first commit
# where a line fails. GitHub names the pull request that brings that
# commit, and its branch `<lane>-<n>-…` names the lane. The watcher files
# one defect for each culprit, naming each red line it brings (#6750), or
# updates the open one, claims it for that lane, and pages that lane's seat
# `FIX`.
#
# The input holds `checks`, the red lines that the culprit brings, each a
# failing check or `check:tests-enforcing <binary> <test>` for one red test
# (`watch_failed`); `check`, one line, as before #6750; `head`, the red head;
# `green`, the last head where the gate passes; `culprit`, the first commit
# where the lines fail; `pr`, its pull request `{number, branch, title}`, or
# null when GitHub names none; `log`, the lines of the gate's log, of which
# `lines.jq` takes each line's own (#6659); and `open`, the open defects
# whose title opens `landing:`, each `{number, title}`.
#
# The output holds `lane`, the culprit's lane, or `triage` when no pull
# request names it; `title`, the defect's title; `number`, the open
# defect that matches the first line, or null when the watcher files a new
# one; `observation`, the body that a new defect opens with under
# `## Observation`, or the comment on the open one; and `page`, the `FIX`
# line, `{n}` standing for the number when the watcher files a new defect.
include "lines";
def short: .[0:9];
. as $in
| ($in.checks // [$in.check]) as $checks
| ($in.pr // null) as $pr
| (if $pr == null then "triage" else ($pr.branch | split("-")[0]) end) as $lane
| "landing: `\($checks[0])`" as $prefix
| (if ($checks | length) == 1 then "\($prefix) fails" else "\($prefix) and \($checks | length - 1) more fail" end) as $red
| ([$in.open[] | select(.title | startswith($prefix + " "))] | first // null) as $match
| (if $pr == null then "commit \($in.culprit | short)" else "#\($pr.number) (\($in.culprit | short))" end) as $brings
| ($checks | map("`\(.)`") | if length == 1 then .[0] else (.[:-1] | join(", ")) + " and " + .[-1] end) as $named
| {
    lane: $lane,
    title: "\($red) from \($brings)",
    number: ($match.number // null),
    observation: (((if $match == null then ["## Observation", ""] else [] end) + [
      "`landing:watch` runs \($named) on the head `\($in.head | short)` of `landing`, and \(if ($checks | length) == 1 then "the check fails" else "each fails" end). \(if ($checks | length) == 1 then "It passes" else "Each passes" end) on `\($in.green | short)`, the last green head.",
      "",
      "The search over the first parents names `\($in.culprit | short)` as the first commit where \(if ($checks | length) == 1 then "the check fails" else "each fails" end). \(if $pr == null then "GitHub names no pull request for it, so the claim goes to the fixer." else "Pull request #\($pr.number), \"\($pr.title)\", brings it, so the claim goes to the lane `\($lane)`." end)",
      ""
    ] + ([$checks[] as $check | [(if ($checks | length) == 1 then "The failing lines:" else "The failing lines of `\($check)`:" end), "", "```text", ($in.log | check_lines($check))[], "```", ""]] | add) | .[:-1] | join("\n"))),
    page: "FIX #\($match.number // "{n}"): \($named) \(if ($checks | length) == 1 then "fails" else "fail" end) on landing at \($in.head | short), and \($brings) brings \(if ($checks | length) == 1 then "it" else "them" end). Repair it on landing, never with a revert."
  }
