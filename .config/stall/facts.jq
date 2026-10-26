# The open pull requests as the stall detector reads them (#2785), from one
# answer to `query.graphql`.
#
# Input: the answer's `repository`.
# Output: `{prs}`, one entry per open pull request:
#   number, draft, head, base, oid  as GitHub names them;
#   bot       an app (Dependabot) opened it: the triage lane closes it and
#             makes its change by hand, so no stall kind reads it;
#   created   when it was opened, in epoch seconds;
#   mergeable `MERGEABLE`, `CONFLICTING` or `UNKNOWN`;
#   queued    whether it is in the merge queue;
#   removals  each time it left the merge queue unmerged: `{at, reason}`;
#   checks    each check run and status on its head: `{name, verdict,
#             conclusion, started, completed}`, the verdict `pass`, `fail` or
#             `pending` read as `.config/pr-stack/required.jq` reads one, the
#             conclusion GitHub's (a status's state).

def epoch: if . == null then null else fromdateiso8601 end;

def verdict:
  if .__typename == "StatusContext" then
    if .state == "SUCCESS" then "pass" elif IN(.state; "PENDING", "EXPECTED") then "pending" else "fail" end
  elif .status != "COMPLETED" and (.conclusion // "") == "" then "pending"
  elif IN(.conclusion; "SUCCESS", "SKIPPED", "NEUTRAL") then "pass"
  else "fail"
  end;

{prs: [.pullRequests.nodes[] | {
  number,
  draft: .isDraft,
  bot: (.author.__typename == "Bot"),
  head: .headRefName,
  base: .baseRefName,
  oid: .headRefOid,
  created: (.createdAt | epoch),
  mergeable,
  queued: .isInMergeQueue,
  removals: [.timelineItems.nodes[] | select(.createdAt != null) | {at: (.createdAt | epoch), reason}],
  checks: [(.commits.nodes[0].commit.statusCheckRollup.contexts.nodes // [])[] | {
    name: (.name // .context),
    verdict: verdict,
    conclusion: (.conclusion // .state),
    started: ((.startedAt // .createdAt) | epoch),
    completed: ((.completedAt // (if .__typename == "StatusContext" then .createdAt else null end)) | epoch)
  }]
}]}
