def forbidden_context:
  capture("\\$\\{\\{[^}]*\\b(?<context>runner|job|steps|env)\\."; "i").context;

# The argument of each `hashFiles` call that walks a build directory: a
# pattern under `target/` with `**`. The expression engine reads every file
# the walk finds within a 120 s budget. So a large build state fails the
# step (#6888).
def build_walks:
  [scan("hashFiles\\(([^)]*)\\)") | .[0]
   | select(test("(^|[^A-Za-z0-9_.-])target/") and test("\\*\\*"))];

# A workflow that runs on an edit of a pull request runs on an edit of its
# body too. So a job there reads a field of `github.event.changes` in its
# condition, and an edit that changes no field it reads skips the job. A job
# with no such field lints the title again on each edit of the body (#6774).
def runs_on_edits:
  (.on | objects | .pull_request // .pull_request_target | objects | .types // [])
  | index("edited") != null;

.workflow as $workflow
| [.jobs
   | to_entries[]
   | .key as $job
   | (.value.env // {})
   | to_entries[]
   | select(.value | type == "string")
   | select(.value | test("\\$\\{\\{[^}]*\\b(runner|job|steps|env)\\."; "i"))
   | .key as $key
   | (.value | forbidden_context) as $context
   | "`\($workflow)` job `\($job)` environment `\($key)` names `\($context).`, unavailable in job env"]
  + [.jobs
   | to_entries[]
   | .key as $job
   | .value
   | ..
   | strings
   | build_walks[]
   | "`\($workflow)` job `\($job)` walks a build directory with `hashFiles(\(.))`. Test one file at the directory's root"]
  + [select(runs_on_edits)
   | .jobs
   | to_entries[]
   | select(.value.if != false)
   | select((.value.if // "" | tostring) | test("github\\.event\\.changes\\.") | not)
   | "`\($workflow)` job `\(.key)` runs on each edit of a pull request. Its condition reads no field of `github.event.changes`"]
