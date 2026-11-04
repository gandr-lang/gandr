# The price of every `gh` call site (#5061), read by `check:gh-budget`.
#
# Input: `{sites, table}`. `sites` is `sites.awk`'s lines as
# `[{file, scope, verb}]`, one per call. `table` is `calls.toml` as JSON:
# `budget`, the hour's ceiling of each identity and API, and `site`, the
# rows. A row names a site (`file`, `scope`), its `api` (`graphql` or
# `rest`), its `identity` (`read` or `write` on a host, `actions` for a
# workflow's token), the `calls` of that API the site holds, the `points`
# one run spends, how they were `measured`, its `trigger`, and `hour`, the
# runs in an hour on one host at eight seats.
#
# Output: one finding a line, nothing when every site is priced.
#
# - A verb's class is its API and whether it reads or writes (`class.jq`).
# - Each site's calls of one API and kind need a row of that API whose
#   identity is the kind, or `actions`, and whose `calls` is their count.
# - A row whose site holds no call of its API and kind is gone.
# - A row's `points` is a whole number. `measured` is `cost` (the
#   `rateLimit` cost of one call), `rest` (one request a call and a page),
#   `log` (the router's call log), `free` (`rate_limit`, at 0 points) or,
#   for a GraphQL write that cannot run to be measured, `rule` (GitHub's
#   floor of one point a request, the requests counted from gh's steps).
# - Each identity's sum of `points * hour` over its rows of one API stays
#   within its `budget`.

include "class";

def key: "\(.file) \(.scope) (\(.api))";

# The kinds an identity covers.
def covers: if . == "actions" then ["read", "write"] else [.] end;

def plural($n): if $n == 1 then "" else "s" end;

# The findings of one row against the groups its site holds.
def row_findings($groups):
  . as $r
  | [$groups[] | select(.file == $r.file and .scope == $r.scope and .api == $r.api and (.kind as $k | $r.identity | covers | index($k)))] as $held
  | ($held | map(.count) | add // 0) as $count
  | (if ($r.identity | IN("read", "write", "actions") | not) then "bad identity: \($r | key) names `\($r.identity)`; one of read, write, actions"
     elif $count == 0 then "gone: \($r | key) as \($r.identity) is in .config/gh/calls.toml, but the site holds no such call"
     elif $r.calls != $count then "changed: \($r | key) as \($r.identity) holds \($count) call\(plural($count)); its row says \($r.calls)"
     else empty end),
    (if ($r.points | type) != "number" or $r.points < 0 or ($r.points | floor) != $r.points then "no measured points: \($r | key) as \($r.identity)"
     elif ($r.measured | IN("cost", "rest", "log", "free", "rule") | not) then "no measure: \($r | key) as \($r.identity) says `\($r.measured)`; one of cost, rest, log, free, rule"
     elif $r.measured == "rule" and ($r.api != "graphql" or $r.identity == "read") then "rule on a read: \($r | key) as \($r.identity) is measured by rule; only a GraphQL write may be"
     elif $r.measured == "free" and $r.points != 0 then "free with points: \($r | key) as \($r.identity) is free, so its points are 0"
     else empty end),
    (if ($r.hour | type) != "number" or $r.hour < 0 then "no bound: \($r | key) as \($r.identity) gives no runs an hour" else empty end),
    (if (($r.trigger // "") | length) == 0 then "no trigger: \($r | key) as \($r.identity)" else empty end);

.table as $table
| ($table.site // []) as $rows
| [.sites[] | . + (.verb | class)] as $calls
| ($calls | group_by([.file, .scope, .api, .kind]) | map({file: .[0].file, scope: .[0].scope, api: .[0].api, kind: .[0].kind, count: length})) as $groups
| ($groups[] as $g
    | select([$rows[] | select(.file == $g.file and .scope == $g.scope and .api == $g.api and (.identity | covers | index($g.kind)))] | length == 0)
    | "unpriced: \($g | key), \($g.count) \($g.kind) call\(plural($g.count)) with no row in .config/gh/calls.toml"),
  ($rows[] | row_findings($groups)),
  ($rows | map(select((.points | type) == "number" and (.hour | type) == "number"))
    | group_by([.identity, .api])[]
    | {identity: .[0].identity, api: .[0].api, spent: (map(.points * .hour) | add), top: (sort_by(-(.points * .hour)) | .[0:3])} as $sum
    | ($table.budget[$sum.identity][$sum.api]) as $ceiling
    | if $ceiling == null then "no ceiling: .config/gh/calls.toml's budget gives none for \($sum.identity) \($sum.api)"
      elif $sum.spent > $ceiling then "over budget: \($sum.identity) \($sum.api) spends \($sum.spent) an hour, over its \($ceiling); the most: \($sum.top | map("\(key) \(.points * .hour)") | join(", "))"
      else empty end)
