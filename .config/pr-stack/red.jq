# The required check that failed on a pull request's head, as `stall:watch`
# reads a red bottom to cut (#5073). A context is read at its newest run, as
# `required.jq` reads it. Only a check run that concluded `FAILURE`, or a
# commit status in the state `FAILURE`, is red: a cancelled, timed-out or
# startup-failed check is the runner's, not the change's, and cuts nothing.
#
# Input: the head's status check rollup, each a `CheckRun` (`name`,
# `status`, `conclusion`, `startedAt`, `detailsUrl`,
# `checkSuite.workflowRun.databaseId`) or a `StatusContext` (`context`,
# `state`, `startedAt`, `targetUrl`).
# Arguments: `$required`, the trunk's required contexts.
# Output: `{check, run}`, the first such context in `$required`'s order and
# the link to its run; `null` when none failed so.

. as $rollup
| [$required[] as $name
    | [$rollup[] | select((.name // .context) == $name)] | sort_by(.checkSuite.workflowRun.databaseId // 0, .startedAt // "") | last // empty
    | select(if .__typename == "StatusContext" then .state == "FAILURE" else .conclusion == "FAILURE" end)
    | {check: $name, run: (.detailsUrl // .targetUrl // null)}]
| first // null
