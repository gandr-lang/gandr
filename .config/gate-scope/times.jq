# The time a gate took (#5215), read from its log. The local gate took 10 to
# 15 minutes on a large change, and nothing recorded the time. CI's time has
# a budget and a check. The local gate's time had neither, so each speed fix
# answered a CI failure and never the local time.
#
# The gate keeps its log, and its record (`passed.bash record`) holds what
# this program reads there. No run is added. mise prints each task's time when
# the task ends (`MISE_TASK_TIMINGS=1`), and the `default` nextest profile
# prints each test's time. A test that two lines name, its result and the
# list of slow tests at the end, counts once. So does a task whose own nested
# `mise run` prints a time under its name: its longest time is its own.
#
# Input:
#   log      the gate's standard error: mise's lines, each task's lines
#            prefixed `[<task>] `
#   seconds  the gate's wall time
#
# Output: {seconds, tasks, suites, tests}. `tasks` gives each task's time,
# the slowest first. `suites` gives each test task's count of tests and their
# summed time, the slowest first. `tests` gives the 20 slowest tests and their
# tasks. Each time is in seconds, to a tenth.

# The seconds in a duration as mise prints it: `259.4ms`, `11.82s`, `1m 2.5s`.
def duration:
  [match("([0-9]+(?:\\.[0-9]+)?)(ns|µs|us|ms|h|m|s)"; "g") | [.captures[].string]
    | (.[0] | tonumber) * {"ns": 0.000000001, "µs": 0.000001, "us": 0.000001, "ms": 0.001, "h": 3600, "m": 60, "s": 1}[.[1]]]
  | add // 0;

def tenths: . * 10 | round / 10;

[.log | gsub("\u001b\\[[0-9;]*m"; "") | split("\n")[] | capture("^\\[(?<task>[^\\]]+)\\] (?<line>.*)$")] as $lines
| ([$lines[] | .task as $task | .line | capture("^Finished in (?<took>.+)$") | {task: $task, seconds: (.took | duration | tenths)}]
  | group_by(.task) | map(max_by(.seconds))) as $tasks
| ([$lines[] | .task as $task | .line
    | capture("^\\s*(?:TRY [0-9]+ )?(?:PASS|SLOW) \\[\\s*(?<took>[0-9]+(?:\\.[0-9]+)?)s\\]\\s+(?:\\(\\s*[0-9]+/[0-9]+\\)\\s+)?(?<test>.+?)\\s*$")
    | {task: $task, test, seconds: (.took | tonumber)}]
  | group_by([.task, .test]) | map(max_by(.seconds))) as $tests
| {
    seconds,
    tasks: ($tasks | sort_by(-.seconds, .task)),
    suites: ($tests | group_by(.task) | map({task: .[0].task, tests: length, seconds: (map(.seconds) | add | tenths)}) | sort_by(-.seconds, .task)),
    tests: ($tests | sort_by(-.seconds, .task, .test) | .[:20] | map(.seconds |= tenths))
  }
