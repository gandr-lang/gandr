# The output of the wide host's measure, read one line at a time. The scaling
# account (`curve.jq`, #6879) reads it so.
#
# The head line, `<tool>: commit <sha>, NUMA nodes <nodes>, mutation run
# <state>`, names the commit that the measure built and whether a mutation run
# held the host. Each point, `|<threads>|<nodes>|<wall times>|<median>|<speed-up>|`,
# gives the wall times in seconds, their median, and the speed-up against one
# thread.

# A number read as a value, so `1.00` is `1`.
def measure_number: tonumber | . + 0;

# The head line as {commit, load}. `load` is `idle`, or `held` while a
# mutation run held the host. Another line gives nothing.
def measure_head:
  capture("^[^ :]+: commit (?<commit>[0-9a-f]{40}), NUMA nodes [^,]+, mutation run (?<load>idle|held)");

# A point as {threads, nodes, walls, median, speedup}, in seconds. Another
# line gives nothing.
def measure_point:
  capture("^\\|(?<threads>[0-9]+)\\|(?<nodes>[0-9,-]+)\\|(?<walls>[0-9. ]+)\\|(?<median>[0-9.]+)\\|(?<speedup>[0-9.]+)\\|$")
  | {threads: (.threads | measure_number), nodes, walls: (.walls | [splits(" +")] | map(select(. != "") | measure_number)),
     median: (.median | measure_number), speedup: (.speedup | measure_number)};

# The outputs in an array of lines, in order, each {commit, load, points}. A
# head line opens an output, and each point after it belongs to that output.
def measure_outputs:
  reduce .[] as $line ([];
    ([$line | measure_head] | first) as $head
    | if $head != null then . + [$head + {points: []}]
      elif length == 0 then .
      else ([$line | measure_point] | first) as $point
        | if $point == null then . else .[-1].points += [$point] end
      end);
