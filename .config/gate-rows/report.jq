# The medians of the gates on one host (#7021), read from the lines of
# `gates.jsonl` that `gate_row` in `.config/mise/gate.bash` appends. A line
# that is no JSON object, as a torn write leaves, is skipped and counted.
#
# Input: the lines of the rows, raw (`jq -R -n`).
# Arguments:
#   $since  the first day of the window, `YYYY-MM-DD` in UTC; empty reads
#           the last 7 days before now
#   $file   the path of the rows, which the header names
# Output: a Markdown table, one row for each gate, class, architecture and
# result, with the count of runs and the median and the 90th percentile of
# their seconds. The median of an even count is the mean of the two middle
# values. The 90th percentile is the value at the rank ceil(0.9 n).

def median:
  sort | length as $n
  | if $n % 2 == 1 then .[($n - 1) / 2] else (.[$n / 2 - 1] + .[$n / 2]) / 2 end;
def percentile($p):
  sort | .[(($p * length) | ceil) - 1];
def tenths: (. * 10 | round) / 10;
def cell: if . == null then "none" else tostring end;

(if $since == "" then now - 7 * 86400 else $since + "T00:00:00Z" | fromdateiso8601 end) as $from
| [inputs | (fromjson? // "torn") | if type == "object" then . else "torn" end] as $lines
| [$lines[] | select(type == "object" and (.start | type) == "number" and (.seconds | type) == "number")] as $rows
| [$rows[] | select(.start >= $from * 1000000)] as $window
| ($from | todateiso8601 | .[:10]) as $day
| [
    "\($window | length) rows of \($rows | length) since \($day) in \($file); \(($lines | length) - ($rows | length)) lines skipped",
    "",
    "|gate|class|arch|result|runs|p50 s|p90 s|",
    "|---|---|---|---|---|---|---|",
    ($window
      | group_by([.gate, .host.class, .host.arch, .result])
      | .[]
      | map(.seconds) as $seconds
      | "|\(.[0].gate)|\(.[0].host.class | cell)|\(.[0].host.arch | cell)|\(.[0].result)|\(length)|\($seconds | median | tenths)|\($seconds | percentile(0.9) | tenths)|")
  ]
| .[]
