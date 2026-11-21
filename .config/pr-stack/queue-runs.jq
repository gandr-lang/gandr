# The failed runs of this pull request's own queue entry since the watch
# began, which `pr:watch` asks for their first failed job (#3745). The queue
# removes an entry whose merge-group run failed, so the run is found by the
# queue's branch for the pull request, `gh-readonly-queue/<trunk>/pr-<n>-…`.
# `gh api` takes no `--arg`, so the filter runs under `jq` (#4225).
#
# Input: one answer of `repos/<repo>/actions/runs?event=merge_group`.
# Arguments: `$prefix`, the queue branch's prefix, and `$since`, the watch's
# start as an ISO 8601 UTC time. Output: each run's id, newest first.
.workflow_runs[]
| select((.head_branch | startswith($prefix)) and .conclusion == "failure" and .created_at >= $since)
| .id
