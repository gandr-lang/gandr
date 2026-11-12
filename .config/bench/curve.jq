# The thread curve that the wide host's measure command prints for one head
# of `main`, read for the scaling account (`bench:scaling`, #6879).
#
# Input: the measure's output, as text. Its first line of the form
# `<tool>: commit <sha>, NUMA nodes <nodes>, mutation run <state>` names the
# commit and whether a mutation run held the host. Each line of its table
# `|<threads>|<nodes>|<wall times>|<median>|<speed-up>|` is one point.
#
# Argument `$widths`: the points the host's configuration names, each
# `{threads, nodes}`, in order. The measure gives exactly these points, or
# the reading refuses, so a row never mixes two layouts of the host.
#
# Output: {commit, load, points}. `load` is `idle`, or `held` while a
# mutation run held the host. Each point is {threads, nodes, walls, median,
# speedup}, in seconds. Each number is read as a value, so `1.00` is `1`.
def number: tonumber | . + 0;
def point:
  capture("^\\|(?<threads>[0-9]+)\\|(?<nodes>[0-9,-]+)\\|(?<walls>[0-9. ]+)\\|(?<median>[0-9.]+)\\|(?<speedup>[0-9.]+)\\|$")
  | {threads: (.threads | number), nodes, walls: (.walls | [splits(" +")] | map(select(. != "") | number)),
     median: (.median | number), speedup: (.speedup | number)};

(split("\n")) as $lines
| ([$lines[] | capture("^[^ :]+: commit (?<commit>[0-9a-f]{40}), NUMA nodes [^,]+, mutation run (?<load>idle|held)")] | first) as $head
| if $head == null then error("the measure names no commit") else . end
| [$lines[] | select(test("^\\|[0-9]")) | point] as $points
| if ($points | map({threads, nodes})) != $widths then
    error("the measure gives the points \($points | map("\(.threads) on \(.nodes)") | join(", ")), not the configured \($widths | map("\(.threads) on \(.nodes)") | join(", "))")
  else . end
| {commit: $head.commit, load: $head.load, points: $points}
