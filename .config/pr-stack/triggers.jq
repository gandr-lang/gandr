# The landing watcher's triggers (#2984): `.github/workflows/landing.yml`
# reads the open pull requests on the events that change what lands, never on
# a schedule, which GitHub ran four to five hours late here. What it must
# carry: `workflow_run` of `CI` on `completed` (a head turning green or red,
# a merge-queue entry passing or failing, `main` moving) and `pull_request`
# on `dequeued` and `ready_for_review`, the two states no completion marks.
#
# Input: the workflow's `on`, as JSON. Output: the refusals, a JSON array of
# lines, empty when the triggers hold.

[if has("schedule") then
   "`schedule`: GitHub ran this repository's schedules four to five hours late, so a reading must follow events, never a cron (#2984)"
 else empty end,
 if ((.workflow_run.workflows // []) | index("CI")) and ((.workflow_run.types // []) | index("completed")) then empty
 else "no `workflow_run` of `CI` on `completed`: a head turning green starts no reading (#2984)" end,
 ((["dequeued", "ready_for_review"] - (.pull_request.types // []))[]
   | "no `pull_request` on `\(.)`: no `CI` completion marks it, so it starts no reading (#2984)")]
