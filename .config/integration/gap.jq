# The gap between `main` and `landing` (#6587), read by `landing:watch`
# each interval. `oldest` is the committer time of the oldest commit on the
# first-parent line of `landing` that `main` lacks, as `brake.jq` reads it,
# or null when `main` holds `landing`. `now` is the time, both in seconds
# since the epoch. `limit` is the minutes past which the gap pages the
# fixer. `main` is the head of `main`, and `paged` is the head of `main` at
# the last page, or null. A gap pages once for each head of `main`: a move
# of `main` starts the gap again.
#
# The output holds the gap in whole minutes, whether to page, the head of
# `main` the page is for, and one line.
. as $in
| (if $in.oldest == null then 0 else (($in.now - $in.oldest) / 60 | floor) end) as $minutes
| {
    minutes: $minutes,
    page: ($minutes > $in.limit and $in.paged != $in.main),
    main: $in.main,
    line: (if $in.oldest == null then "main holds landing"
           else "main stands \($minutes) minutes behind landing at \($in.main[0:9])" end)
  }
