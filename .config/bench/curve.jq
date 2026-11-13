# The thread curve that the wide host's measure command prints for one head
# of `main`, read for the scaling account (`bench:scaling`, #6879).
#
# Input: the measure's output, as text, which `measure.jq` reads. Its first
# head line names the commit and whether a mutation run held the host. Each
# point of its table is one point of the curve.
#
# Argument `$widths`: the points the host's configuration names, each
# `{threads, nodes}`, in order. The measure gives exactly these points, or
# the reading refuses, so a row never mixes two layouts of the host.
#
# Output: {commit, load, points}. `load` is `idle`, or `held` while a
# mutation run held the host. Each point is {threads, nodes, walls, median,
# speedup}, in seconds. Each number is read as a value, so `1.00` is `1`.
include "measure";

(split("\n")) as $lines
| ([$lines[] | measure_head] | first) as $head
| if $head == null then error("the measure names no commit") else . end
| [$lines[] | select(test("^\\|[0-9]")) | measure_point] as $points
| if ($points | map({threads, nodes})) != $widths then
    error("the measure gives the points \($points | map("\(.threads) on \(.nodes)") | join(", ")), not the configured \($widths | map("\(.threads) on \(.nodes)") | join(", "))")
  else . end
| {commit: $head.commit, load: $head.load, points: $points}
