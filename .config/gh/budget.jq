# The price of every `gh` call site (#5061), read by `check:gh-budget`.
#
# Input: `{sites, table, schedules}`. `sites` is `sites.awk`'s lines as
# `[{file, scope, verb, paginated}]`, one per call, `paginated` true for a
# call that gives `--paginate`. `table` is `calls.toml` as JSON: `budget`,
# the hour's ceiling of each identity and API, and `site`, the rows. A row
# names a site (`file`, `scope`), its `api` (`graphql` or `rest`), its
# `identity` (`read` or `write` on a host, `actions` for a workflow's
# token, `cycle` for the `gandr-lang` App), the `calls` of that API the
# site holds, the `points` one run spends, how they were `measured`, its
# `trigger`, and `hour`, the runs in an hour on one host at eight seats.
# A row of a site that reads pages states `pages`, the pages its lists read
# in one run (#5681). A row that a workflow's cron runs names the workflow
# as `schedule`, a file name or a list of them. `schedules` gives each such
# workflow's crons.
#
# Output: one finding a line, nothing when every site is priced.
#
# - A verb's class is its API and whether it reads or writes (`class.jq`).
# - Each site's calls of one API and kind need a row of that API whose
#   identity is the kind, or a token that reads and writes (`actions`,
#   `cycle`), and whose `calls` is their count.
# - A row whose site holds no call of its API and kind is gone.
# - A row's `points` is a whole number. `measured` is `cost` (the
#   `rateLimit` cost of one call), `rest` (one request a call and a page),
#   `log` (the router's call log), `free` (`rate_limit`, at 0 points) or,
#   for a GraphQL write that cannot run to be measured, `rule` (GitHub's
#   floor of one point a request, the requests counted from gh's steps).
# - A row whose site reads pages states `pages`, a whole number no larger
#   than its `points`. A row whose site reads no pages states none.
# - A row with a `schedule` spends only in the UTC hours its workflows'
#   crons name. A row with none spends in each hour.
# - In each of the 24 hours, each identity's sum of `points * hour` over its
#   rows of one API stays within its `budget`. A finding names the worst
#   hour, or says `an hour` when every hour sums the same.

include "class";

def key: "\(.file) \(.scope) (\(.api))";

# The kinds an identity covers: a workflow's token and the `gandr-lang` App
# each read and write.
def covers: if . == "actions" or . == "cycle" then ["read", "write"] else [.] end;

def plural($n): if $n == 1 then "" else "s" end;

# The UTC hours a cron's hour field names, ascending, or null for a cron
# this rule does not read. The field is a list of `*`, `N` or `A-B`, each
# with an optional `/step`.
def cron_hours:
  (split(" ") | map(select(. != ""))) as $field
  | if ($field | length) != 5 then null
    else [$field[1] | split(",")[]
        | (capture("^(?<from>\\*|[0-9]+)(-(?<to>[0-9]+))?(/(?<step>[0-9]+))?$") // null)
        | if . == null then null
          else (if .from == "*" then 0 else .from | tonumber end) as $a
          | (if .to != null then .to | tonumber elif .from == "*" or .step != null then 23 else $a end) as $b
          | ((.step // "1") | tonumber) as $s
          | if $b > 23 or $a > $b or $s < 1 then null else [range($a; $b + 1; $s)] end
          end]
      | if any(.[]; . == null) then null else add | unique end
    end;

# The hours a row spends in, as `{hours, findings}`: `hours` null for every
# hour, which a row with no `schedule` or a refused one takes.
def row_hours($schedules):
  . as $r
  | if $r.schedule == null then {hours: null, findings: []}
    else [[$r.schedule] | flatten[] | . as $workflow
        | ($schedules[$workflow] // []) as $crons
        | if ($crons | length) == 0 then {finding: "no schedule: \($r | key) as \($r.identity) names `\($workflow)`, which runs on no cron"}
          else $crons[] | . as $cron | cron_hours as $hours
            | if $hours == null then {finding: "bad cron: \($r | key) as \($r.identity): `\($workflow)` runs at `\($cron)`, an hour field this rule does not read"}
              else {hours: $hours} end
          end] as $parts
      | ($parts | map(.finding // empty)) as $findings
      | {hours: (if ($findings | length) > 0 then null else $parts | map(.hours[]) | unique end), findings: $findings}
    end;

# The findings of one row against the groups its site holds.
def row_findings($groups; $schedules):
  . as $r
  | [$groups[] | select(.file == $r.file and .scope == $r.scope and .api == $r.api and (.kind as $k | $r.identity | covers | index($k)))] as $held
  | ($held | map(.count) | add // 0) as $count
  | ($held | any(.[]; .paginated)) as $paged
  | (if ($r.identity | IN("read", "write", "actions", "cycle") | not) then "bad identity: \($r | key) names `\($r.identity)`; one of read, write, actions, cycle"
     elif $count == 0 then "gone: \($r | key) as \($r.identity) is in .config/gh/calls.toml, but the site holds no such call"
     elif $r.calls != $count then "changed: \($r | key) as \($r.identity) holds \($count) call\(plural($count)); its row says \($r.calls)"
     else empty end),
    (if ($r.points | type) != "number" or $r.points < 0 or ($r.points | floor) != $r.points then "no measured points: \($r | key) as \($r.identity)"
     elif ($r.measured | IN("cost", "rest", "log", "free", "rule") | not) then "no measure: \($r | key) as \($r.identity) says `\($r.measured)`; one of cost, rest, log, free, rule"
     elif $r.measured == "rule" and ($r.api != "graphql" or $r.identity == "read") then "rule on a read: \($r | key) as \($r.identity) is measured by rule; only a GraphQL write may be"
     elif $r.measured == "free" and $r.points != 0 then "free with points: \($r | key) as \($r.identity) is free, so its points are 0"
     else empty end),
    (if $count == 0 then empty
     elif $paged and $r.pages == null then "no pages: \($r | key) as \($r.identity) reads pages; its row states no `pages`"
     elif $r.pages == null then empty
     elif ($r.pages | type) != "number" or $r.pages < 1 or ($r.pages | floor) != $r.pages then "bad pages: \($r | key) as \($r.identity) states `pages` \($r.pages); a whole number of 1 or more"
     elif ($paged | not) then "pages unread: \($r | key) as \($r.identity) states `pages`, but the site reads no pages"
     elif ($r.points | type) == "number" and $r.points < $r.pages then "pages over points: \($r | key) as \($r.identity) reads \($r.pages) pages, over its \($r.points) points"
     else empty end),
    ($r | row_hours($schedules) | .findings[]),
    (if ($r.hour | type) != "number" or $r.hour < 0 then "no bound: \($r | key) as \($r.identity) gives no runs an hour" else empty end),
    (if (($r.trigger // "") | length) == 0 then "no trigger: \($r | key) as \($r.identity)" else empty end);

def two: if . < 10 then "0\(.)" else tostring end;

.table as $table
| (.schedules // {}) as $schedules
| ($table.site // []) as $rows
| [.sites[] | . + (.verb | class)] as $calls
| ($calls | group_by([.file, .scope, .api, .kind])
    | map({file: .[0].file, scope: .[0].scope, api: .[0].api, kind: .[0].kind, count: length, paginated: any(.[]; .paginated == true)})) as $groups
| ($groups[] as $g
    | select([$rows[] | select(.file == $g.file and .scope == $g.scope and .api == $g.api and (.identity | covers | index($g.kind)))] | length == 0)
    | "unpriced: \($g | key), \($g.count) \($g.kind) call\(plural($g.count)) with no row in .config/gh/calls.toml"),
  ($rows[] | row_findings($groups; $schedules)),
  ($rows | map(select((.points | type) == "number" and (.hour | type) == "number") | . + {hours: (row_hours($schedules) | .hours)})
    | group_by([.identity, .api])[]
    | . as $priced
    | [range(0; 24) as $h
        | [$priced[] | select(.hours == null or (.hours | index($h)) != null)] as $in
        | {hour: $h, spent: ($in | map(.points * .hour) | add // 0), top: ($in | sort_by(-(.points * .hour)) | .[0:3])}] as $hours
    | ($hours | sort_by(-.spent) | .[0]) as $worst
    | ($priced[0] | {identity, api}) as $id
    | ($table.budget[$id.identity][$id.api]) as $ceiling
    | if $ceiling == null then "no ceiling: .config/gh/calls.toml's budget gives none for \($id.identity) \($id.api)"
      elif $worst.spent > $ceiling then
        (if ($hours | map(.spent) | unique | length) == 1 then "an hour" else "in the hour from \($worst.hour | two):00 UTC" end) as $when
        | "over budget: \($id.identity) \($id.api) spends \($worst.spent) \($when), over its \($ceiling); the most: \($worst.top | map("\(key) \(.points * .hour)") | join(", "))"
      else empty end)
