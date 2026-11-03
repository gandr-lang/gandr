# The claim `claim:next` writes and the claim it keeps (#4660). Two runs
# that both read the pick before either writes would both claim it, so the
# write keeps another lane's claim marker standing before its own
# (`markers.jq`'s `claiming`), and the run reads the body once more after
# it. The first claim marker is the earlier claim, and it holds the issue.
#
# Input:
#   lane  the lane claiming, a key of `.config/issues/lanes.toml`
#   step  `write`, before the write; `check`, after it
#   body  the issue's body as GitHub holds it at the step, or null
#
# Output: under `write`, `{body}`, the body to write. Under `check`,
# `{kept: true}` when the lane's marker is the first, else `{kept: false,
# body}`, the body without the lane's marker for the run to write back, or
# null when its write left none.

include "markers";

.lane as $lane
| if .step == "write" then {body: (.body | claiming($lane))}
  elif (.body | claim_lane) == $lane then {kept: true}
  else {kept: false, body: (.body | unclaiming($lane))}
  end
