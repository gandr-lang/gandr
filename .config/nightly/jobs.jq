# The nightly's container jobs (#3208). Each job that runs in the CI image
# pays a container start of 20 to 25 s, so a job that restores no build state
# and builds nothing of its own work is a step of the one `reports` job, never
# a job of its own. In that job a failing step hides none after it: every step
# after `setup rust` runs unless the run was cancelled, and the lane budget,
# which refuses a night past its ceiling, is the last step.
#
# Input: `.github/workflows/nightly.yml`'s `jobs`, anchors expanded, as JSON.
# Output: the refusals, a JSON array of lines, empty when the jobs hold.

def stateless: (.steps // []) | all(.name != "restore complete test state");

[to_entries[]
  | select(.key != "template" and (.value.container // null) != null and (.value | stateless))
  | .key] as $stateless
| ($stateless - ["reports"]) as $extra
| (.reports.steps // []) as $steps
| ($steps | map(.name) | index("setup rust")) as $setup
| [($extra[]
    | "`\(.)` starts the CI image and restores no build state: a container start is 20 to 25 s, so it is a step of `reports`, not a job (#3208)"),
   (if $setup == null then empty
    else $steps[$setup + 1:][]
      | select((.if // "") | contains("!cancelled()") | not)
      | "`reports` step `\(.name // .uses)` runs only while every step before it passed: give it `if: ${{ !cancelled() }}` so a failing step hides none after it (#3208)"
    end),
   (if ($steps | length) > 0 and ($steps | last | .name) != "compare each lane with its budget"
    then "`reports` ends with `\($steps | last | .name)`: the lane budget, which refuses a night past its ceiling, runs last so its refusal hides no other step (#3208)"
    else empty end)]
