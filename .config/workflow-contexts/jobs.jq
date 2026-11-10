def forbidden_context:
  capture("\\$\\{\\{[^}]*\\b(?<context>runner|job|steps|env)\\."; "i").context;

[.workflow as $workflow
 | .jobs
 | to_entries[]
 | .key as $job
 | (.value.env // {})
 | to_entries[]
 | select(.value | type == "string")
 | select(.value | test("\\$\\{\\{[^}]*\\b(runner|job|steps|env)\\."; "i"))
 | .key as $key
 | (.value | forbidden_context) as $context
 | "`\($workflow)` job `\($job)` environment `\($key)` names `\($context).`, unavailable in job env"]
