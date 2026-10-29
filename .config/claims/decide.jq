# The claim lifecycle (#1270): which claimed issues lose `status:claimed`,
# one `number<TAB>reason` line each.
#
# Input:
#   now           the reading's time, in seconds since the epoch
#   claimed       the issues carrying the label, open or closed:
#                 [{number, state, labels: [name], claimed_at}], claimed_at
#                 when the label was last added
#   open_prs      the open pull requests: [{number, body, head}]
#   merged_body   the body of the pull request that just merged, or null
#
# With a merged body, the claim comes off every issue the body advances
# (`Advances #n`: that slice is done, and a seat working the next one claims
# it again) or closes (`Closes`, `Fixes` or `Resolves #n`: GitHub closes the
# issue and leaves its labels). Every run, a merge's and the sweep's, then
# reads the rest: a closed issue keeps no claim, a `kind:epic` issue is never
# claimed, and a claim whose label is 4 hours old that no open pull request
# names (one of those keywords in its body, or the number in its branch) has
# no seat on it: a unit that runs past 4 hours should have been rescoped
# (#2534). The age is the label's, never the issue's last update: a comment, a
# reference or another label leaves it alone, so a claim nobody works lapses
# however busy its issue is (#3915). The merge's run reads silence too,
# because GitHub's schedule runs the sweep far less often than it states.

include "targets";

def silent($now): ($now - (.claimed_at | fromdateiso8601)) >= 14400;

.now as $now
| .open_prs as $prs
| (if .merged_body != null then .merged_body | targets("advances") else [] end) as $advanced
| (if .merged_body != null then .merged_body | targets(closing) else [] end) as $closed
| .claimed[]
| . as $issue
| .number as $n
| if ($advanced | index($n)) then "\($n)\tadvanced"
  elif ($closed | index($n)) then "\($n)\tclosed"
  elif .state == "closed" then "\($n)\tclosed"
  elif (.labels | index("kind:epic")) then "\($n)\tepic"
  elif silent($now) and ([$prs[] | names($issue.number)] | any | not) then "\($n)\tsilent"
  else empty
  end
