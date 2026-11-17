# Whether a head that the CI depth gate stopped (#5074) still holds its CI run
# cancelled, so that the watcher's promotion may run it again (#5171). Only
# the required contexts of the landing-checks workflow are read. The gate cancels that
# run alone. A context of another workflow, such as the title check, runs
# beside the cancelled run, and its conclusion never counts. A required job
# whose condition excludes a pull request, such as the brake on `landing`,
# skips in every run of a pull request, so its skip never counts either.
#
# Input: the head's status check rollup, each a `CheckRun` (`name`,
# `conclusion`, `checkSuite.workflowRun.workflow.name`) or a `StatusContext`
# (`context`), which no workflow run carries.
# Arguments: `$required`, the trunk's required contexts; `$workflow`, the
# name of the landing-checks workflow, the `name` of `.github/workflows/landing-checks.yml`.
# Output: `true` when no required context of the landing-checks workflow holds a
# conclusion other than `CANCELLED` or `SKIPPED`, or runs again; `false`
# otherwise.

[.[]
  | select(.checkSuite.workflowRun.workflow.name == $workflow)
  | select((.name // .context) as $name | $required | index($name))
  | select(.conclusion | IN("CANCELLED", "SKIPPED") | not)]
| length == 0
