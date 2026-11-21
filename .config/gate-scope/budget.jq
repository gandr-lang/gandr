# Whether main's gate kept its budget (#5215). Each test has a time bound,
# and the suite had none, so a sweep that stayed under 30 s passed and the
# sum grew unread. The gate on main runs every check over the whole
# workspace, so its time compares from one run to the next. `budget.json`
# holds its budget, and `report:gate-time` reads this verdict.
#
# Input:
#   record  the newest record of a gate on main's tree, with its `time`
#           (`times.jq`)
#   budget  `budget.json`: each gate's budget, in seconds
#
# Output: {over, observation, fields}. `over` is true when the gate took
# longer than its budget, and false for a gate without a budget. The
# observation gives the time, the budget, the five slowest tasks and the ten
# slowest tests. `fields` fills the `gate-time` template.

.record as $record
| .budget[$record.gate] as $budget
| $record.time as $time
| {
    over: ($budget != null and $time.seconds > $budget),
    observation: ([
      "## Observation",
      "",
      "`mise run \($record.gate)` took \($time.seconds) s on main's tree `\($record.tree)`, at `\($record.commit[:12])`. \(if $budget == null then "It has no budget in" else "Its budget is \($budget) s in" end) `.config/gate-scope/budget.json`.",
      "",
      "The table gives the five slowest tasks.",
      "",
      "| Task | Seconds |",
      "| ---- | ------- |",
      ($time.tasks[:5][] | "| `\(.task)` | \(.seconds) |"),
      "",
      "The table gives the ten slowest tests.",
      "",
      "| Task | Test | Seconds |",
      "| ---- | ---- | ------- |",
      ($time.tests[:10][] | "| `\(.task)` | `\(.test)` | \(.seconds) |")
    ] | join("\n") + "\n"),
    fields: {
      seconds: "\($time.seconds)",
      budget: (if $budget == null then "none" else "\($budget)" end),
      task: ($time.tasks[0].task // "none"),
      test: ($time.tests[0].test // "none")
    }
  }
