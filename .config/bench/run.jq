# One run that the wide host's measure command prints, read for the scaling
# account (`bench:scaling`, #6879): a run of `gandr check` at one width, or a
# run of the hotpath series.
#
# Input: the measure's output, as text. Its last line of the form
# `<tool>: exit <status>, wall <seconds> s` gives the run's status and wall
# time. A line `<tool>: past bound` says the run met the host's memory bound.
#
# Output: {status, wall, bound}. `bc` writes a wall under one second with no
# leading zero, as `.98`. A run whose output holds no such line refuses: the
# measure ended before the run did.
(split("\n")) as $lines
| ([$lines[] | capture("^[^ :]+: exit (?<status>[0-9]+), wall (?<wall>[0-9]*\\.?[0-9]+) s$")] | last) as $end
| if $end == null then error("the measure gives no exit and wall time") else . end
| {status: ($end.status | tonumber), wall: ($end.wall | if startswith(".") then "0" + . else . end | tonumber | . + 0),
   bound: any($lines[]; test("^[^ :]+: past bound"))}
