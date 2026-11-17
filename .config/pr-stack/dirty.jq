# Whether a `DIRTY` merge state is a conflict (#2854), as `pr:watch` reads
# it. GitHub computes a pull request's merge state lazily after a push to it
# or below it, so one reading taken while its stack is restacked can be
# stale. A `DIRTY` reading therefore counts only when the next poll repeats
# it at the same head, as a removal from the queue counts only when the next
# poll repeats it (the watch's `gone`).
#
# Input: an object with
#   status  the pull request's `mergeStateStatus`;
#   head    the head it was read at;
#   seen    the head of the previous poll's unconfirmed `DIRTY`, or null.
# Output: `{act, seen}`, `seen` being what the next poll passes in. `act` is
# `conflict` for a `DIRTY` repeated at the same head, `confirm` for a first
# one or one at a head that moved since, which waits a poll, and `clear` for
# any other merge state.

if .status != "DIRTY" then {act: "clear", seen: null}
elif .seen == .head then {act: "conflict", seen: null}
else {act: "confirm", seen: .head}
end
