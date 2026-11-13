# The run whose jobs `ci:cycle` reads before its decision (#6887), or null.
# The input is the dispatched runs of ci.yml on `integration`, newest first,
# each run that the step has read marked `hollow` or not. The step reads the
# jobs of the run that this program names, marks it, and asks again, so a
# hollow failure that opens its head gives way to the run below it
# (`verdicts.jq`).
include "verdicts";

unread
