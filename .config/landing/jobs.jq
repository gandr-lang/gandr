# The queue on `landing` runs the blocking set alone (#5439). A merge group
# on `landing` runs the jobs that run the tasks of `check:landing`, the
# brake (#5442) and the jobs that they need, which are the run's setup.
# Every other job that a merge group can run skips a group on `landing`. The
# blocking jobs run each task of `check:landing` and no other check. A pull
# request on `landing` runs no Clippy, because its author ran
# `check:landing` before `pr:open`.
#
# The program reads a job's `if` as text. A job can run in a merge group when
# its `if` names `merge_group`, or when it holds no `github.event_name ==`
# test. A job skips a group on `landing` when its `if` holds `skip`. A job
# runs a check for each `mise run check:<name>` in its steps, and it is the
# brake when a step runs `mise run ci:brake`.
#
# The same merge group uploads no build state, and main's push reads it as
# its queue run (#6790). So each build state that the nightly restores
# needs a job that saves it (a step `cache complete test state`, the state
# its `CI_BUILD_STATE`) on a push whose queue run holds none: its `if` holds
# `!contains(…, 'build-state-<state>--')`. Without it, no run of main writes
# the state, and each night builds cold.
#
# A push to `landing` runs the report lanes alone (#6993): each job whose
# `if` names `landed == 'true'` or the push to `landing`, the jobs they need,
# and the jobs that read them. Any other job that can run on that push is a
# fault. A job can run on it when its `if` holds no `github.event_name ==`
# test, or tests `== 'push'` other than as main's push, or tests another
# event with `!=`. Its `if` holds `landed != 'true'` or `github.event_name !=
# 'push'` to skip it. The fault applies only when `pushes`, the branches of
# the workflow's `on.push`, holds `landing`.
#
# Input: `{jobs, landing, states, pushes}`. `jobs` is
# `.github/workflows/landing-checks.yml`'s `jobs`, anchors expanded. `landing` is the
# list of tasks that `check:landing` depends on. `states` is the build states
# that `.github/workflows/nightly-sweeps.yml` restores, none when absent. `pushes`
# is the branches of `on.push`, none when absent.
# Output: the refusals, a JSON array of lines, empty when the jobs hold.

def skip: "github.event.merge_group.base_ref != 'refs/heads/landing'";

def pull: "github.base_ref != 'landing'";

def condition: (.if // "") | tostring;

def grouped:
  condition as $if
  | $if != "false" and (($if | test("merge_group")) or ($if | test("github\\.event_name == ") | not));

def skips: condition | contains(skip);

def checks: [(.steps // [])[] | (.run // "") | tostring | scan("\\bmise run (check:[a-z0-9-]+)") | .[0]] | unique;

def brakes: any((.steps // [])[]; (.run // "") | tostring | test("\\bmise run ci:brake(?![\\w:-])"));

def needed: (.needs // []) | if type == "string" then [.] else . end;

def saves($state):
  (.env.CI_BUILD_STATE // "") == $state
  and any((.steps // [])[]; (.name // "") == "cache complete test state");

def unheld($state): "!contains(join(fromJSON(needs.prepare.outputs.artifacts || '[]'), ' '), 'build-state-\($state)--')";

def closure($jobs):
  . as $names
  | ([$names[] | ($jobs[.] // {}) | needed[]] + $names | unique) as $next
  | if $next == $names then $names else $next | closure($jobs) end;

def landed: "needs.prepare.outputs.landed != 'true'";

def main_push: "github.event_name == 'push' && github.ref == 'refs/heads/main'";

def reports: condition | (contains("needs.prepare.outputs.landed == 'true'") or contains("github.ref == 'refs/heads/landing'"));

def pushes:
  (condition | gsub(main_push; "")) as $if
  | ($if | contains(landed) or contains("github.event_name != 'push'")) as $skipped
  | (condition | test("github\\.event_name == ") | not) as $eventless
  | ($if | contains("github.event_name == 'push'") or contains("github.event_name != '")) as $pushed
  | ($skipped | not) and ($eventless or $pushed);

.landing as $landing
| .jobs as $jobs
| [$jobs | to_entries[] | select(.key != "template" and (.value | grouped) and (.value | skips | not))] as $running
| [$running[] | select((.value | checks | length > 0) or (.value | brakes))] as $blocking
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
    | "`\(.key)` runs Clippy on a pull request on `landing`: add `\(pull)` to its `if` (#5439)"),
  ((.states // [])[] as $state
    | select(any($jobs[]; saves($state) and (condition | contains(unheld($state)))) | not)
    | "no job saves `\($state)` on a push to main whose queue run holds none, so the nightly restores no state and builds cold: add `\(unheld($state))` to the `if` of the job that saves it (#6790)"),
  (if (.pushes // []) | index("landing") then
     ([$jobs | to_entries[] | select(.value | reports) | .key]) as $lanes
     | ($lanes | closure($jobs)) as $reached
     | $jobs
     | to_entries[]
     | select(.key != "template" and (.key | IN($reached[]) | not))
     | select(any(.value | needed[]; IN($lanes[])) | not)
     | select(.value | pushes)
     | "`\(.key)` can run on a push to `landing` outside its report lanes: add `\(landed)` to its `if` (#6993)"
   else empty end)]
