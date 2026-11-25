# The date of each range of one file (#2891), for `report:dead-weight`'s
# `Since` column. Input: {porcelain, ranges}: the output of
# `git blame --porcelain` with one `-L <start>,<end>` for each range, and the
# ranges as [start, end] pairs. Output: {"<start>-<end>": "YYYY-MM-DD"}: for
# each range, the UTC date of the newest commit that last touched one of its
# lines. A line that the blame does not give leaves its range out.
(.porcelain | split("\n")
  | reduce .[] as $line ({commit: null, times: {}, lines: {}};
      if $line | test("^[0-9a-f]{40} [0-9]+ [0-9]+") then
        ($line | split(" ")) as $head | .commit = $head[0] | .lines[$head[2]] = $head[0]
      elif $line | startswith("committer-time ") then
        .times[.commit] = ($line | ltrimstr("committer-time ") | tonumber)
      else . end)) as $blame
| [ .ranges[] | [range(.[0]; .[1] + 1) | tostring | $blame.lines[.] // empty | $blame.times[.] // empty] as $times
    | select($times | length > 0)
    | {key: "\(.[0])-\(.[1])", value: ($times | max | strftime("%Y-%m-%d"))} ]
| from_entries
