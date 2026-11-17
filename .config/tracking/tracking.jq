# A refusal in the tree points at what resolves it (#2529): one line per
# refusal, or nothing.
#
# Input:
#   constants  every `TrackingIssue` constant of `crates/core-term/src/failure.rs`:
#              [{name, number}]
#   rows       the features ledger's `declined` rows: [{id, refs: [n]}]
#   states     each number's state: {"<n>": {kind, state, reason, landed}},
#              `kind` `issue` or `pull`, `state` `OPEN`, `CLOSED` or
#              `MERGED`, `reason` an issue's `stateReason`; a number naming
#              nothing is absent. `landed` is on an issue closed as
#              completed that a commit closes: true when a commit in the
#              history of HEAD closes it, false when only a commit on another
#              remote branch closes it (#5778)
#
# An unimplemented refusal names its `TrackingIssue`, and every face shows it
# (#1207): the issue whose landing builds the feature, so it is open; or the
# decision not to build it, an issue closed as not planned. An issue closed as
# completed tracks nothing when a commit in HEAD closes it, or when no commit
# closes it. While only a commit on another remote branch closes it, the tree
# does not hold its landing yet, as on `main` before a promotion, and the
# issue holds. A pull request is no feature's issue. A declined row of the
# ledger names its decision on the same terms.

def holds: . != null and .kind == "issue" and (.state == "OPEN" or .reason == "NOT_PLANNED" or .landed == false);
def described:
  if . == null then "names nothing"
  elif .kind == "pull" then "is a pull request"
  else "is closed as \(.reason // "completed" | ascii_downcase | gsub("_"; " "))"
  end;

.states as $states
| ((.constants // [])[]
    | ($states[.number | tostring]) as $s
    | select($s | holds | not)
    | "crates/core-term/src/failure.rs: `TrackingIssue::\(.name)` names #\(.number), which \($s | described): name the open issue whose landing builds the feature, or the decision closed as not planned"),
  ((.rows // [])[]
    | select(any(.refs[]; $states[tostring] | holds) | not)
    | "ledger/features.sql: the declined row `\(.id)` names \(if (.refs | length) == 0 then "no issue" else (.refs | map("#\(.)") | join(", ")) + ", " + (.refs | map(($states[tostring] | described)) | join("; ")) end): name its decision, an issue closed as not planned")
