# The repair that a pull request on `landing` states (#7078), read by
# `ci:cycle` on a step whose verdict fails on the tip of `integration` while
# no tag `integration-repair` stands. The input holds `runs`, the dispatched
# runs of landing-checks.yml on `integration`, newest first, and `merges`, the merges of
# the queue on `landing` past `integration`, newest first, each with its
# commit, its pull request and the request's body.
#
# A body states a repair with one line `Repairs integration at <head>`, the
# head 7 to 40 hexadecimal digits. The line binds when its head starts a head
# that fails since the newest pass, so a line of an older red takes nothing.
# The output is the newest merge whose body holds a bound line, as the repair
# that `cycle.jq` reads, `{sha, held, from}`, or null.
include "verdicts";

def stated: [scan("(?m)^Repairs integration at ([0-9a-f]{7,40})[ \\t\\r]*$")[0]];

. as $in
| ($in.runs | verdicts | (((map(.conclusion == "success") | index(true)) // length) as $n | .[0:$n]) | map(.headSha)) as $failed
| first($in.merges[] | select(any((.body // "") | stated[]; . as $head | any($failed[]; startswith($head))))) // null
| if . == null then null else {sha, held: true, from: .number} end
