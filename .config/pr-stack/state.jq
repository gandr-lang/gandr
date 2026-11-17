# A stack member's readiness to queue (#2783), the state `prefix.jq` reads
# it by. GitHub's stack merge adds the members up to the one it is given
# atomically, and refuses the whole add when one of them conflicts: a green
# root below a conflicting member was dropped with it, and nothing landed. So
# a conflicting member cuts the prefix as a red one does, whatever its checks
# read, and its conflict is named first: a rebase reruns its checks.
#
# Input: an object with
#   mergeable  the pull request's `mergeable`: `MERGEABLE`, `CONFLICTING` or
#              `UNKNOWN` while GitHub computes it;
#   failed     its required contexts that failed (`required.jq`);
#   pending    its required contexts not yet concluded (`required.jq`).
# Output: `conflicting`, `red`, `pending` or `green`. An `UNKNOWN`
# mergeability is read by the checks alone, as before #2783: GitHub settles
# it within seconds of a push, and the stack merge reads it again.

if .mergeable == "CONFLICTING" then "conflicting"
elif .failed != [] then "red"
elif .pending != [] then "pending"
else "green"
end
