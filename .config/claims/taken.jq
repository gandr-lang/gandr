# The claim a lane holds on the unit it works (#5146). A lane that works a
# unit without a claim leaves the issue free, so `claim:next` gives it to
# another lane. The gate reads the claim of the unit its branch works, and
# `claim:take` writes the claim of a unit the lane names.
#
# A unit branch is `<lane>-<n>-…` or `<lane>-<n>`. The lane is the longest key
# of `.config/issues/lanes.toml` the branch starts with before `-<n>`, else the
# letters before the first number, in segments of letters (`sorts-3403-chain`).
# A branch with a `/` or with no number works no unit.
#
# Input:
#   step    `branch`, `gate` or `take`
#   branch  under `branch` and `gate`, the branch the gate runs on, or ""
#   lanes   under `branch` and `gate`, the keys of `lanes.toml`
#   lane    under `take`, the lane that takes the claim
#   issue   under `gate` and `take`, `{number, state, labels, body}` as GitHub
#           holds it, or null when the read failed
#
# Output: under `branch`, `{lane, number}`, or null for a branch that works no
# unit. Under `gate`, `{verdict}`: `none` for no unit, `held` when the lane
# holds the claim, `closed` for a closed issue, and `unread` or `refused` with
# the `line` the gate prints. Under `take`, `{verdict}`: `write` with the
# `body` to write, `held` when the lane holds the claim already, or `refused`
# with the `line` `claim:take` prints.

include "markers";

# The unit `$branch` works, `{lane, number}`, or null.
def unit_branch($branch; $lanes):
  if ($branch | test("^[a-z][a-z0-9-]*$") | not) then null
  else
    ([$lanes[] | . as $lane
      | ($branch | capture("^\($lane)-(?<number>[0-9]+)(?:-|$)")) // empty
      | {lane: $lane, number: (.number | tonumber), length: ($lane | length)}]
     | max_by(.length) // null | if . then del(.length) else null end)
    // ($branch | capture("^(?<lane>[a-z]+(?:-[a-z]+)*)-(?<number>[0-9]+)(?:-|$)")
        | {lane, number: (.number | tonumber)})
    // null
  end;

# The lane whose claim `$issue` carries: `status:claimed` and the lane its
# first claim marker names. Null when it carries no claim.
def holder($issue):
  if ($issue.labels | index("status:claimed")) then ($issue.body | claim_lane) else null end;

if .step == "branch" then unit_branch(.branch; .lanes)
elif .step == "gate" then
  unit_branch(.branch; .lanes) as $unit
  | if $unit == null then {verdict: "none"}
    elif .issue == null then
      {verdict: "unread", line: "check: \(.branch) works #\($unit.number), and its issue could not be read, so its claim goes unchecked; the next gate reads it again"}
    elif .issue.state == "closed" then {verdict: "closed"}
    else holder(.issue) as $holder
      | if $holder == $unit.lane then {verdict: "held"}
        elif $holder == null then
          {verdict: "refused", line: "check: \(.branch) works #\($unit.number), and #\($unit.number) holds no claim of \($unit.lane), so claim:next can give it to another lane; run \u0060mise run claim:take \($unit.number)\u0060 and gate again"}
        else
          {verdict: "refused", line: "check: \(.branch) works #\($unit.number), and \($holder) holds its claim, not \($unit.lane); the coordinator decides which lane works it"}
        end
    end
elif .step == "take" then
  .lane as $lane
  | if .issue.state == "closed" then
      {verdict: "refused", line: "claim:take: #\(.issue.number) is closed; a closed issue takes no claim"}
    else holder(.issue) as $holder
      | if $holder == $lane then {verdict: "held"}
        elif $holder != null then
          {verdict: "refused", line: "claim:take: \($holder) holds the claim of #\(.issue.number); the coordinator decides which lane works it"}
        else {verdict: "write", body: (.issue.body | claiming($lane))}
        end
    end
else error("taken.jq: no step `\(.step)`")
end
