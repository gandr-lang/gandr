# The integration cycle's decision (#5440), read by `ci:cycle`. The input
# holds the tips of `landing` and `integration`, GitHub's comparison of
# `integration...landing` (`ahead`, `behind`, `identical` or `diverged`), and
# the newest dispatched runs of ci.yml on `integration`, newest first.
#
# The verdict is the newest run that completed with a pass or a failure. A
# cancelled run gives no verdict. While a run is queued or in progress,
# nothing moves: the end of that run starts the next cycle. Otherwise
# `integration` takes the tip of `landing`. It fast-forwards when it holds no
# commit past `landing`, and the merges API merges `landing` into it when it
# holds the fixer's commits. A tip that moves is tested. A tip that stands is
# tested once, when no verdict names it yet.
def failed: . == "failure" or . == "timed_out" or . == "startup_failure";
def short: .[0:12];

. as $in
| ($in.runs | map(select(.status == "completed" and (.conclusion == "success" or (.conclusion | failed))))
  | first
  | if . == null then null else {id: .databaseId, url, sha: .headSha, conclusion} end) as $verdict
| ($in.runs | any(.status != "completed")) as $running
| if $running then
    {take: "none", dispatch: false, line: "A cycle runs on integration. The end of that run starts the next cycle."}
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
