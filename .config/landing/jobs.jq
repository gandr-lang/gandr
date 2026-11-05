# The queue on `landing` runs the blocking set alone (#5439). A merge group
# on `landing` runs the jobs that run the tasks of `check:landing` and the
# jobs that they need, which are the run's setup. Every other job that a merge
# group can run skips a group on `landing`. The blocking jobs run each task of
# `check:landing` and no other check. A pull request on `landing` runs no
# Clippy, because its author ran `check:landing` before `pr:open`.
#
# The program reads a job's `if` as text. A job can run in a merge group when
# its `if` names `merge_group`, or when it holds no `github.event_name ==`
# test. A job skips a group on `landing` when its `if` holds `skip`. A job
# runs a check for each `mise run check:<name>` in its steps.
#
# Input: `{jobs, landing}`. `jobs` is `.github/workflows/ci.yml`'s `jobs`,
# anchors expanded. `landing` is the list of tasks that `check:landing`
# depends on.
# Output: the refusals, a JSON array of lines, empty when the jobs hold.

def skip: "github.event.merge_group.base_ref != 'refs/heads/landing'";

def pull: "github.base_ref != 'landing'";

def condition: (.if // "") | tostring;

def grouped:
  condition as $if
  | $if != "false" and (($if | test("merge_group")) or ($if | test("github\\.event_name == ") | not));

def skips: condition | contains(skip);

def checks: [(.steps // [])[] | (.run // "") | tostring | scan("\\bmise run (check:[a-z0-9-]+)") | .[0]] | unique;

def needed: (.needs // []) | if type == "string" then [.] else . end;

def closure($jobs):
  . as $names
  | ([$names[] | ($jobs[.] // {}) | needed[]] + $names | unique) as $next
  | if $next == $names then $names else $next | closure($jobs) end;

.landing as $landing
| .jobs as $jobs
| [$jobs | to_entries[] | select(.key != "template" and (.value | grouped) and (.value | skips | not))] as $running
| [$running[] | select(.value | checks | length > 0)] as $blocking
| ([$blocking[].key] | unique | closure($jobs)) as $allowed
| ([$blocking[].value | checks[]] | unique) as $run
| [($running[]
    | select(.key | IN($allowed[]) | not)
    | "`\(.key)` runs in a merge group on `landing` outside the blocking set: add `\(skip)` to its `if` (#5439)"),
  ($blocking[]
    | .key as $job
    | (.value | checks)[]
    | select(IN($landing[]) | not)
    | "`\($job)` runs `\(.)` in a merge group on `landing`, and `check:landing` does not name it: name it there, or skip the job on `landing` (#5439)"),
  ($landing[]
    | select(IN($run[]) | not)
    | "`check:landing` names `\(.)`, and no job runs it in a merge group on `landing`: run it in a blocking job, or take it off the list (#5439)"),
  (if any($jobs[]; .name == "check Clippy wall") | not
   then "no job is named `check Clippy wall`, the check that the ruleset of `landing` requires (#5439)"
   else empty end),
  ($jobs
    | to_entries[]
    | select(.value.name == "check Clippy wall" and (.value | condition | contains(pull) | not))
    | "`\(.key)` runs Clippy on a pull request on `landing`: add `\(pull)` to its `if` (#5439)")]
