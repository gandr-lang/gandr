# The claim lifecycle (#1270): which claimed issues lose `status:claimed`,
# one `number<TAB>reason` line each.
#
# Input:
#   now           the reading's time, in seconds since the epoch
#   claimed       the issues carrying the label, open or closed:
#                 [{number, state, labels: [name], claimed_at, lane,
#                 released}], claimed_at when the label was last added, lane
#                 the body's claim marker or null, released the body's
#                 release `{lane, at}` with `at` in seconds, or null
#   open_prs      the open pull requests: [{number, body, head}]
#   merged_body   the body of the pull request that just merged, or null
#
# With a merged body, the claim comes off every issue the body closes
# (`Closes`, `Fixes` or `Resolves #n`: GitHub closes the issue and leaves its
# labels). An issue the body advances (`Advances #n`) keeps its claim while it
# stays open: a unit of several landings keeps its lane between them (#6954).
# Every run, a merge's and the sweep's, then reads the rest: a closed issue
# keeps no claim, a `kind:epic` issue is never claimed, and a claim 4 hours
# old that no open pull request names (one of those keywords in its body, or
# the number in its branch) has no seat on it: a unit that runs past 4 hours
# should have been rescoped (#2534). The age is the label's, never the issue's
# last update: a comment, a reference or another label leaves it alone, so a
# claim nobody works lapses however busy its issue is (#3915). A merge that
# advances the unit writes a release of the claim's own lane, and the age
# counts from that release when it is later (#6954). The merge's run reads
# silence too, because GitHub's schedule runs the sweep far less often than
# it states.

include "targets";

# The time a claim's age counts from: its label's addition, or a later
# release of the claim's own lane, which a merge writes (#6954).
def since: . as $claim
  | [($claim.claimed_at | fromdateiso8601), ($claim.released // empty | select(.lane == $claim.lane) | .at)] | max;

def silent($now): ($now - since) >= 14400;

.now as $now
| .open_prs as $prs
| (if .merged_body != null then .merged_body | targets(closing) else [] end) as $closed
| .claimed[]
| . as $issue
| .number as $n
| if ($closed | index($n)) then "\($n)\tclosed"
  elif .state == "closed" then "\($n)\tclosed"
  elif (.labels | index("kind:epic")) then "\($n)\tepic"
  elif silent($now) and ([$prs[] | names($issue.number)] | any | not) then "\($n)\tsilent"
  else empty
  end
