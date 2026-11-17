# The verdicts of the integration cycle (#5440), which `cycle.jq`,
# `brake.jq` and `hollow.jq` include. The input is the dispatched runs of
# landing-checks.yml on `integration`, newest first. A verdict is a run that completed with
# a pass or a failure. A cancelled run gives no verdict.
#
# A hollow failure gives no verdict either, once for its head (#6887). It is a
# run that completes with `failure` while no job of it ends `failure` or
# `timed_out`, as when a job finds no runner. `ci:cycle` reads the jobs of
# such a run and marks it `hollow`. A run opens its head when no older run
# failed on that head. Only a hollow failure that opens its head is set aside,
# so a second failure on one head gives a verdict, hollow or not.
def failed: . == "failure" or . == "timed_out" or . == "startup_failure";
def completed: map(select(.status == "completed" and (.conclusion == "success" or (.conclusion | failed))));
def opened: . as $runs
  | [range(length) as $i | $runs[$i]
     | .opening = ([$runs[$i + 1:][] | select(.headSha == $runs[$i].headSha and (.conclusion | failed))] == [])];
def aside: .conclusion == "failure" and .opening and .hollow == true;
def verdicts: completed | opened | map(select(aside | not) | del(.opening));
# The runs set aside above the newest verdict, newest first.
def set_aside: completed | opened | ((map(aside) | index(false)) // length) as $n | .[0:$n] | map(del(.opening));
# The run whose jobs the step reads next, or null: the newest run that is not
# set aside, when it fails with `failure`, opens its head and holds no mark.
def unread: (first(completed | opened | .[] | select(aside | not)) // null)
  | if . != null and .conclusion == "failure" and .opening and (has("hollow") | not) then .databaseId else null end;
