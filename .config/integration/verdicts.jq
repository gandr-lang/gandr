# The verdicts of the integration cycle (#5440), which `cycle.jq` and
# `brake.jq` include. The input is the dispatched runs of ci.yml on
# `integration`, newest first. A verdict is a run that completed with a pass
# or a failure. A cancelled run gives no verdict.
def failed: . == "failure" or . == "timed_out" or . == "startup_failure";
def verdicts: map(select(.status == "completed" and (.conclusion == "success" or (.conclusion | failed))));
