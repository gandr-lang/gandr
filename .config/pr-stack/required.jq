# The trunk's required contexts on a pull request's head, read before its
# stack queues (#1601). Only the required contexts are read, so a check the
# rules do not require, such as the mutants report, never holds the landing.
# A context is read at its newest workflow run, then at that run's newest
# start: a re-run attempt keeps its run and starts later than the attempt it
# replaces. A re-run of an older run never outranks a newer run, whenever it
# starts (#5777): the newer run answers the newer event, such as an edited
# title. A check run that carries a conclusion is read by it whatever its
# status says: GitHub has recorded a finished job as still in progress beside
# its conclusion (#1858).
#
# With `--arg workflow <name>`, the head's own run of that workflow, its
# newest, is read whole too (#7549): each of its jobs that ended `FAILURE`
# fails the reading, required or not. A report, a job whose name starts
# `report `, never fails it. A job of that run that has not ended is not
# read, so nothing waits on a job that the rules do not require, and a
# cancelled, timed-out or startup-failed job is the runner's, as `red.jq`
# reads it. The required contexts stay the rules' own: a red job ends the
# wait at once, and no other job holds it.
#
# Input: the head's status check rollup, each a `CheckRun` (`name`,
# `status`, `conclusion`, `startedAt`, `checkSuite.workflowRun.databaseId`,
# and `checkSuite.workflowRun.workflow.name` for `$workflow`) or a
# `StatusContext` (`context`, `state`, `startedAt`), which has no run.
# Arguments: `$required`, the trunk's required contexts; optionally
# `--argjson gated true` for a head the CI depth gate stopped (#5074), whose
# cancelled checks wait for its promotion and are pending, not failed;
# optionally `--arg workflow`, the head's own workflow.
# Output: `{failed, pending}`, the required contexts that concluded
# otherwise than success, skipped or neutral, then the jobs of the own run
# that ended red, and the required contexts not yet concluded or not yet
# reported, each in `$required`'s order and the run's jobs by name. Both
# empty: the stack may queue.

def verdict:
  if .__typename == "StatusContext" then
    if .state == "SUCCESS" then "pass" elif IN(.state; "PENDING", "EXPECTED") then "pending" else "fail" end
  elif .status != "COMPLETED" and (.conclusion // "") == "" then "pending"
  elif .conclusion == "CANCELLED" and ($ARGS.named.gated // false) then "pending"
  elif IN(.conclusion; "SUCCESS", "SKIPPED", "NEUTRAL") then "pass"
  else "fail"
  end;

. as $rollup
| [$required[] as $name
    | {name: $name,
       verdict: ([$rollup[] | select((.name // .context) == $name)] | sort_by(.checkSuite.workflowRun.databaseId // 0, .startedAt // "")
         | if length == 0 then "pending" else last | verdict end)}]
| ([$rollup[] | select(.__typename == "CheckRun" and .checkSuite.workflowRun.workflow.name? == ($ARGS.named.workflow // null))]) as $own
| ($own | map(.checkSuite.workflowRun.databaseId // 0) | max // null) as $run
| ([$own[] | select((.checkSuite.workflowRun.databaseId // 0) == $run)] | group_by(.name)
  | map(sort_by(.startedAt // "") | last | select(.conclusion == "FAILURE") | .name
      | select(startswith("report ") | not) | select(IN($required[]) | not))) as $red
| {failed: ([.[] | select(.verdict == "fail") | .name] + $red), pending: [.[] | select(.verdict == "pending") | .name]}
