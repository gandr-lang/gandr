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
# Input: the head's status check rollup, each a `CheckRun` (`name`,
# `status`, `conclusion`, `startedAt`, `checkSuite.workflowRun.databaseId`)
# or a `StatusContext` (`context`, `state`, `startedAt`), which has no run.
# Arguments: `$required`, the trunk's required contexts; optionally
# `--argjson gated true` for a head the CI depth gate stopped (#5074), whose
# cancelled checks wait for its promotion and are pending, not failed.
# Output: `{failed, pending}`, the required contexts that concluded
# otherwise than success, skipped or neutral, and those not yet concluded or
# not yet reported, each in `$required`'s order. Both empty: the stack may
# queue.

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
| {failed: [.[] | select(.verdict == "fail") | .name], pending: [.[] | select(.verdict == "pending") | .name]}
