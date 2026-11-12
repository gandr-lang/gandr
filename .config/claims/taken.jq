# The claim a lane holds on the unit it works (#5146). A lane that works a
# unit without a claim leaves the issue free, so `claim:next` gives it to
# another lane. The gate reads the claim of the unit its branch works, and
# `claim:take` writes the claim of a unit the lane names.
#
# A unit branch is `<lane>-<n>-…` or `<lane>-<n>`. The lane is the longest key
# of the factory's lane table the branch starts with before `-<n>`, else the
# letters before the first number, in segments of letters (`sorts-3403-chain`).
# A branch with a `/` or with no number works no unit.
#
# Input:
#   step    `branch`, `gate`, `take` or `release`
#   branch  under `branch` and `gate`, the branch the gate runs on, or ""
#   lanes   under `branch` and `gate`, the keys of the factory's lane table
#   lane    under `take` and `release`, the lane that acts on the claim
#   now     under `take`, the time of the take in seconds
#   issue   under `gate`, `take` and `release`, `{number, state, labels, body}` as GitHub
#           holds it, or null when the read failed
#
# Output: under `branch`, `{lane, number}`, or null for a branch that works no
# unit. Under `gate`, `{verdict}`: `none` for no unit, `held` when the lane
# holds the claim, `closed` for a closed issue, `mark` with the `body` to
# write and the `line` the gate prints, and `unread` or `refused` with the
# `line` the gate prints. Under `take`, `{verdict}`: `write` with the
# `body` to write, `held` when the lane holds the claim already, or `refused`
# with the `line` `claim:take` prints. Under `release`, it is `release` when
# the lane holds the claim, or `refused` with the line `claim:release` prints.
#
# An issue under `status:claimed` with no claim marker lost its marker to an
# edit of its body (#6210). The label stands, so a lane holds it. The gate of
# the lane whose branch works it writes that lane's marker back (`mark`), and
# `claim:take` refuses it, so a second lane never takes it in the gap.
#
# A merge that advances an open issue, and `claim:release` without `--forgo`,
# write a release marker (`claims.sh`). The lane it names keeps the issue for
# 2 hours (`kept`). `claim:take` refuses the issue to every other lane in that
# time, as `claim:next` passes it over, so a pool's pins never give a unit of
# several landings to a second lane between two landings (#6954).

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
        elif $holder == null and (.issue.labels | index("status:claimed")) then
          # No live marker stands, so the gate appends the lane's own after the
          # text and changes nothing else, a marker quoted in a fence included.
          {verdict: "mark", body: ((.issue.body // "" | sub("\\s+$"; "")) + "\n\n" + claim_marker($unit.lane) + "\n"),
           line: "check: #\($unit.number) carries status:claimed and no claim marker, as an edit of its body dropped it; the gate writes the marker of \($unit.lane) back (#6210)"}
        elif $holder == null then
          {verdict: "refused", line: "check: \(.branch) works #\($unit.number), and #\($unit.number) holds no claim of \($unit.lane), so claim:next can give it to another lane; run \u0060mise run claim:take \($unit.number)\u0060 and gate again"}
        else
          {verdict: "refused", line: "check: \(.branch) works #\($unit.number), and \($holder) holds its claim, not \($unit.lane); the coordinator decides which lane works it"}
        end
    end
elif .step == "take" then
  .lane as $lane
  | .now as $now
  | if .issue.state == "closed" then
      {verdict: "refused", line: "claim:take: #\(.issue.number) is closed; a closed issue takes no claim"}
    else holder(.issue) as $holder
      | if $holder == $lane then {verdict: "held"}
        elif $holder != null then
          {verdict: "refused", line: "claim:take: \($holder) holds the claim of #\(.issue.number); the coordinator decides which lane works it"}
        elif (.issue.labels | index("status:claimed")) then
          {verdict: "refused", line: "claim:take: #\(.issue.number) carries status:claimed and no claim marker: an edit of its body dropped the marker of the lane that works it, and that lane's next gate writes it back; the coordinator decides which lane works it (#6210)"}
        elif ([.issue.body | kept($now) | .lane != $lane] | any) then
          (.issue.body | kept($now)) as $kept
          | {verdict: "refused", line: "claim:take: \($kept.lane) released #\(.issue.number) at \($kept.at | todate), and keeps it until \($kept.at + 7200 | todate) for its next landing. To move it, the coordinator runs `claim:take \(.issue.number) --lane \($kept.lane)`, then `claim:release \($kept.lane) \(.issue.number) --forgo`, then `claim:take \(.issue.number) --lane \($lane)` (#6954)"}
        # A body without the label keeps no lapsed lane's marker (#5531).
        else {verdict: "write", body: (.issue as $issue | $issue.body | claiming($lane; $issue.labels))}
        end
    end
elif .step == "release" then
  .lane as $lane
  | holder(.issue) as $holder
  | if $holder == $lane then {verdict: "release"}
    elif $holder == null then
      {verdict: "refused", line: "claim:release: #\(.issue.number) holds no claim of \($lane)"}
    else
      {verdict: "refused", line: "claim:release: \($holder) holds the claim of #\(.issue.number). The task leaves it unchanged"}
    end
else error("taken.jq: no step `\(.step)`")
end
