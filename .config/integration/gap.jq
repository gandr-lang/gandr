# The gap between `main` and `landing` (#6587), read by `landing:watch`
# each interval. `oldest` is the committer time of the oldest commit on the
# first-parent line of `landing` that `main` lacks, as `brake.jq` reads it,
# or null when `main` holds `landing`. `now` is the time, both in seconds
# since the epoch. `limit` is the minutes past which the gap pages the
# fixer. `main` and `integration` are the heads of those branches. A cycle
# runs while `integration` holds a commit that `main` lacks, and
# `integration` names the cycle. `paged` is the last page of the gap,
# `{main, cycle, minutes}`, or null.
#
# A gap past the limit pages the fixer once for one head of `main`. It
# pages again only when the cycle changes, or when the gap grows by 30
# minutes past the last page. A move of `main` starts the gap again. The
# page goes to the coordinator too only when no cycle runs.
#
# The output holds the gap in whole minutes, whether to page, whether the
# coordinator gets the page, the page's `{main, cycle, minutes}`, and one
# line.
. as $in
| (if $in.oldest == null then 0 else (($in.now - $in.oldest) / 60 | floor) end) as $minutes
| ($in.integration != $in.main) as $running
| (if $running then $in.integration else null end) as $cycle
| ($in.paged // null) as $last
| {
    minutes: $minutes,
    page: ($minutes > $in.limit
      and ($last == null or $last.main != $in.main or $last.cycle != $cycle or $minutes >= $last.minutes + 30)),
    coordinator: ($running | not),
    paged: {main: $in.main, cycle: $cycle, minutes: $minutes},
    line: (if $in.oldest == null then "main holds landing"
           elif $running then "main stands \($minutes) minutes behind landing at \($in.main[0:9]), and the cycle on integration \($in.integration[0:9]) runs"
           else "main stands \($minutes) minutes behind landing at \($in.main[0:9]), and no cycle runs" end)
  }
