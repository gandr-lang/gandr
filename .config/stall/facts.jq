# The open pull requests as the stall detector reads them (#2785), from one
# answer to `query.graphql`, the latest merged ones' refactoring verdicts
# beside the refactor issues filed for them (#2885), and the claimed issues'
# areas (#3822) and lanes (#4174).
#
# Input: the answer's `repository`; `merged`, `refactors` and `claimed`
# absent read as none.
# Output: `{prs, merged, filed, claimed}`; `prs` one entry per open pull
# request:
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
#             conclusion GitHub's (a status's state);
# `merged` one entry per merged pull request read, `{number, head, merged,
# verdict, rows}`: when it merged, in epoch seconds, its `## Refactoring`
# verdict (`yes`, `maybe`, `no` or null) and how many rows its table names;
# `filed` the pull requests a `kind:refactor` issue's `from:` line names;
# `claimed` one entry per open `status:claimed` issue, `{number, areas,
# lane}`: its `area:` labels, and the lane its claim marker names
# (`markers.jq`'s `claim_lane`), null for a claim with no marker.

include "sections";
include "markers";

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
}],
 merged: [(.merged.nodes // [])[] | (.body // "" | refactoring) as $r | {
   number,
   head: .headRefName,
   merged: (.mergedAt | epoch),
   verdict: $r.verdict,
   rows: ($r.rows // [] | length)
 }],
 filed: [(.refactors.nodes // [])[] | .body // "" | from_lines[]] | unique,
 claimed: [(.claimed.nodes // [])[] | {number, areas: [.labels.nodes[].name | select(startswith("area:"))], lane: (.body | claim_lane)}]}
