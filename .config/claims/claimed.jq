# The claim `claim:next` writes, the claim it keeps (#4660), and the body a
# lapsed claim leaves (#5531). Two runs that both read the pick before either
# writes would both claim it, so under `status:claimed` the write keeps
# another lane's claim marker standing before its own (`markers.jq`'s
# `claiming`), and the run reads the body once more after it. The first
# claim marker is the earlier claim, and it holds the issue. A live claim
# adds its label before its marker, so a read without the label shows no
# live marker, and the write keeps none.
#
# A body edit keeps the markers the body held (#6210): `issue:edit` writes a
# seat's new body with each marker the old one carried and the new one lacks.
#
# Input:
#   lane    the lane claiming, a key of `.config/issues/lanes.toml`; under
#           `lapse`, the lane whose claim lapses; under `edit`, unread
#   step    `write`, before the write; `check`, after it; `lapse`, after the
#           sweep takes the lapsed label off; `edit`, before a body edit
#   labels  under `write`, the labels of the read before the write
#   body    the issue's body as GitHub holds it at the step, or null; under
#           `edit`, the new body
#   old     under `edit`, the body as GitHub holds it before the edit
#
# Output: under `write`, `{body}`, the body to write. Under `check`,
# `{kept: true}` when the lane's marker is the first, else `{kept: false,
# body}`, the body without the lane's marker for the run to write back, or
# null when its write left none. Under `lapse`, `{body}`, the body without
# the lane's marker, or null when it carries none: a later claim wrote over
# it, and the sweep writes nothing. Under `edit`, `{body}`, the new body with
# each marker the old one kept.

include "markers";

.lane as $lane
| if .step == "write" then
    if .labels == null then error("claimed.jq: the write reads the issue's labels")
    else .labels as $labels | {body: (.body | claiming($lane; $labels))}
    end
  elif .step == "check" then
    if (.body | claim_lane) == $lane then {kept: true}
    else {kept: false, body: (.body | unclaiming($lane))}
    end
  elif .step == "lapse" then {body: (.body | unclaiming($lane))}
  elif .step == "edit" then .old as $old | {body: (.body | keeping($old))}
  else error("claimed.jq: no step `\(.step)`")
  end
