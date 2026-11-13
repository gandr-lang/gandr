# The integration cycle's decision (#5440), read by `ci:cycle`. The input
# holds the tips of `landing` and `integration`, GitHub's comparison of
# `integration...landing` (`ahead`, `behind`, `identical` or `diverged`), and
# the newest dispatched runs of ci.yml on `integration`, newest first.
#
# The verdict is the newest run that completed with a pass or a failure. A
# cancelled run gives no verdict. While a run is queued or in progress,
# nothing moves: the end of that run starts the next cycle. While the verdict
# is a failure, `integration` takes nothing from `landing` (#5829): each
# commit of the fixer is tested alone, and `landing` waits for a pass. One
# failure takes `landing` all the same (#6560): the verdict names the tip of
# `integration`, so no commit of the fixer waits for its test, and `landing`
# holds the repair that the fixer marks (`repair`, `{sha, held}`, `held` when
# `landing` holds the commit). A repair that only `landing` carries, such as a
# revert that the fixer may not make on `integration`, otherwise waits with no
# end. The decision then carries `repaired`, and `ci:cycle` drops the mark
# after the take.
# Otherwise `integration` takes the tip of `landing`. It fast-forwards when it
# holds no commit past `landing`, and the merges API merges `landing` into it
# when it holds the fixer's commits. A tip that moves is tested. A tip that
# stands is tested once, when no verdict names it yet.
# A hollow failure that opens its head gives no verdict (#6887, `verdicts.jq`).
# The decision's branches then rerun the suite on the tip, or take `landing` when
# it holds new commits. The decision names each such run in `aside`, and its
# line says that the run gives no verdict.
include "verdicts";

def short: .[0:12];

. as $in
| ($in.runs | verdicts
  | first
  | if . == null then null else {id: .databaseId, url, sha: .headSha, conclusion} end) as $verdict
| ($in.runs | set_aside | map({id: .databaseId, url, sha: .headSha})) as $aside
| ($in.runs | any(.status != "completed")) as $running
| if $running then
    {take: "none", dispatch: false, line: "A cycle runs on integration. The end of that run starts the next cycle."}
  elif $verdict != null and ($verdict.conclusion | failed) and ($in.compare == "ahead" or $in.compare == "diverged") then
    if $verdict.sha == $in.integration and ($in.repair.held // false) then
      {take: (if $in.compare == "ahead" then "fast-forward" else "merge" end), dispatch: true, repaired: true, line: "Run \($verdict.id) fails on the tip of integration, \($in.integration | short), and landing, \($in.landing | short), holds its repair, \($in.repair.sha | short), so integration takes landing, and the suite starts."}
    elif $verdict.sha == $in.integration then
      {take: "none", dispatch: false, line: "Run \($verdict.id) fails on the tip of integration, \($in.integration | short), so landing, \($in.landing | short), waits for a fix."}
    else
      {take: "none", dispatch: true, line: "Run \($verdict.id) fails on \($verdict.sha | short), so landing, \($in.landing | short), waits for a fix. No verdict names the tip of integration, \($in.integration | short), so the suite starts."}
    end
  elif $in.compare == "ahead" then
    {take: "fast-forward", dispatch: true, line: "integration fast-forwards to the tip of landing, \($in.landing | short), and the suite starts."}
  elif $in.compare == "diverged" then
    {take: "merge", dispatch: true, line: "The tip of landing, \($in.landing | short), merges into integration, and the suite starts."}
  elif $verdict == null or $verdict.sha != $in.integration then
    {take: "none", dispatch: true, line: "No verdict names the tip of integration, \($in.integration | short), so the suite starts."}
  else
    {take: "none", dispatch: false, line: "A verdict names the tip of integration, \($in.integration | short), and landing holds nothing new."}
  end
| {verdict: $verdict} + .
| if $aside == [] then .
  else .aside = $aside
    | .line = ([$aside[] | "Run \(.id) fails on \(.sha | short) with no failed job, so it gives no verdict once for its head."] + [.line] | join(" "))
  end
