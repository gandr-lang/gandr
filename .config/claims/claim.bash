# The claim of each design page a unit marks primary (#6569, `claim.jq`),
# sourced by `unit:check` and `issue:file` after
# `.config/references/vault.bash`.
#
# `claim_check <body> <before>` prints the lines of `claim.jq`: a refusal
# for each row of a `design` or `partly` page that lacks a part of the claim,
# or a `note:` where `<before>`, the body as it stood when the rule landed,
# holds the same `## Sources`. `<before>` is JSON: a string, or null.
#
# `claim_before <issue>` prints that body as JSON, or null when the issue
# did not carry `shape:signed` when the rule landed. The rule lands with
# the first commit on the first-parent line that adds `claim.jq`. One
# GraphQL read takes the body's edits, the first of them its text at
# creation, and the issue's label events.

claim_check() {
  local claims=${BASH_SOURCE[0]%/*}
  jq -n --arg body "$1" --argjson absorption "$(vault_absorption)" --argjson before "$2" \
    '{body: $body, absorption: $absorption, before: $before}' \
    | jq -r -L "$claims" -f "$claims/claim.jq"
}

claim_before() {
  local claims=${BASH_SOURCE[0]%/*} since
  since=$(git -C "$claims" log -1 --first-parent --diff-filter=A --format=%ct -- claim.jq)
  # A checkout whose history holds no commit adding the rule (a shallow
  # clone) reads the rule as landing now, so no signed unit is refused.
  [[ -n $since ]] || since=$(date +%s)
  gh api graphql -F owner='{owner}' -F name='{repo}' -F number="$1" -f query='
    query($owner: String!, $name: String!, $number: Int!) {
      repository(owner: $owner, name: $name) {
        issue(number: $number) {
          createdAt
          body
          userContentEdits(last: 100) { nodes { editedAt diff } }
          timelineItems(itemTypes: [LABELED_EVENT], last: 100) { nodes { ... on LabeledEvent { createdAt label { name } } } }
        }
      }
    }' \
    | jq -c --argjson since "$since" '.data.repository.issue as $issue
      | ($since | todate) as $at
      | if any($issue.timelineItems.nodes[]; .label.name == "shape:signed" and .createdAt <= $at) | not then null
        else ([$issue.userContentEdits.nodes[] | select(.editedAt <= $at)] | sort_by(.editedAt) | last | .diff)
          // (if $issue.createdAt <= $at then $issue.body else null end)
        end'
}
