# The open issues and pull requests, read once for every report that needs
# them (#5681). The nightly's reports job writes the list to a file and sets
# `OPEN_ISSUES` to it for each report. So `report:deps`, `report:design`
# and `report:prose` share 8 pages of 719 open items on 2026-11-06, in place
# of 8 pages each. A report that runs by hand, with `OPEN_ISSUES` unset,
# reads the list itself through the same function.

# Writes the open issues and pull requests of the repository `$1` to the file
# `$2`, one JSON array of `{number, title, labels, body, pull_request}`.
# `labels` holds the label names, and `pull_request` is true for a pull
# request. The file that `OPEN_ISSUES` names, when it is set, stands in for
# the read.
open_issues() {
  if [[ -n ${OPEN_ISSUES:-} ]]; then
    cp -- "$OPEN_ISSUES" "$2"
    return
  fi
  gh api --paginate "repos/$1/issues?state=open&per_page=100" \
    --jq '[.[] | {number, title, labels: [.labels[].name], body: (.body // ""), pull_request: (.pull_request != null)}]' \
    | jq -s 'add // []' > "$2"
}
