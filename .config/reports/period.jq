# The period `report:obligations` reads (#3576). Input: {since, until}, two
# dates YYYY-MM-DD. Output: {days, previous}: every day from since to until,
# both included, which the task searches one at a time, and the month before
# since's, {since, until}, the period of the report the month's first run
# closes. The dates are read here rather than by `date -d`, which is GNU's
# alone, so a hand run on any host reads the period the nightly reads. A date
# that is not a calendar day as written, or a period that ends before it
# starts, is refused.
def day: . as $date
  | (try (strptime("%Y-%m-%d") | mktime) catch null) as $time
  | if $time != null and ($time | todate[:10]) == $date then $time
    else error("not a date YYYY-MM-DD: \($date)") end;
def date: todate[:10];
(.since | day) as $since
| (.until | day) as $until
| if $since > $until then error("the period ends before it starts: \(.since) to \(.until)") else . end
| ((.since[:7] + "-01" | day) - 86400) as $last
| {days: [range($since; $until + 1; 86400) | date],
   previous: {since: (($last | date[:7]) + "-01"), until: ($last | date)}}
