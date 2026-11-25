# The open issues and pull requests, read once for every reader that needs
# them (#5681, #5671). The nightly's reports job writes the list to a file
# and sets `OPEN_ISSUES` to it for each report. So `report:deps`,
# `report:design` and `report:prose` share 8 pages of 719 open items on
# 2026-11-06, in place of 8 pages each. `claim:next`, `issue:labels --sweep`
# and a report that runs by hand, with `OPEN_ISSUES` unset, read the list
# through the same function.

# Writes the open issues and pull requests of the repository `$1` to the file
# `$2`, one JSON array of `{number, title, labels, body, pull_request,
# blocked, parent}`. `$1` is `owner/name`, or gh's `{owner}/{repo}`, which
# gh fills (#5749). `labels` holds the label names, and `pull_request` is
# true for a pull request. `blocked` is the count of issues that block the
# item, from GitHub's dependency summary. `parent` is the number of its parent
# issue in the item's own repository, or null. The file that `OPEN_ISSUES`
# names, when it is set, stands in for the read.
open_issues() {
  if [[ -n ${OPEN_ISSUES:-} ]]; then
    cp -- "$OPEN_ISSUES" "$2"
    return
  fi
  gh api --paginate "repos/$1/issues?state=open&per_page=100" \
    --jq '[.[] | {number, title, labels: [.labels[].name], body: (.body // ""), pull_request: (.pull_request != null),
      blocked: (.issue_dependencies_summary.blocked_by // 0),
      parent: (.repository_url as $own | .parent_issue_url // "" | if startswith($own + "/issues/") then ltrimstr($own + "/issues/") | tonumber else null end)}]' \
    | jq -s 'add // []' > "$2"
}
