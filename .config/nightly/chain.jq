# The chain of one cold build (#6893), read from Cargo's build analysis log
# (`-Zbuild-analysis`). The log registers each unit with the units it
# depends on, and it records when each unit starts, when its metadata is
# ready, when its code generation starts (`-Zsection-timings`) and when it
# ends. `--timings` keeps only the unit that unblocked each other unit, so
# the log is the record that holds every edge.
#
# The chain is the longest path through the units by their whole durations.
# A unit's slack is how far its own path falls short of the chain: the time
# by which the unit can grow before the chain grows. Under pipelining a unit
# starts on the metadata of a dependency, so the chain's pipelined time
# counts each unit up to the point at which the next unit on the chain
# started on it. A dependent that started before its dependency ended waited
# on the metadata. Any other dependent waited on the whole unit.
#
# The metric of a split (#6893, accepted on 2026-11-12) reads three inputs
# for each crate of the chain. The row gives two of them: the crate's front
# end, from its start to the start of its code generation, and the bound of
# a split. The bound is the time that the chain loses when the unit takes
# no time at all, so no split of the unit takes more off the chain. The
# third input, the crate's edits in a week, comes from the history
# (`report:chain`), and the row names each unit's source in the workspace
# for it.
#
# Input: the log's records, slurped into one array. The `build-started`
#   record's `cwd` is the workspace's root.
# Argument: $top, the count of the longest units off the chain that the row
#   names with their slack.
# Output: the row `{units, wall, time, in_flight, longest, length, pipelined,
#   chain, off, times}`. Each time is in seconds, to the hundredth. `chain`
#   lists `{unit, source, seconds, front, bound, waits}` from the first unit
#   to the last. `source` is the unit's directory under the workspace's
#   root, or `null` for a dependency from outside it. `front` is `null` for a
#   unit with no code generation, such as the run of a build script. `waits`
#   is how the next unit on the chain waited on it (`metadata` or `whole`,
#   `null` for the last). `off` lists `{unit, seconds, slack}`. `times` maps
#   each unit to its duration, for the next night's comparison.
# A log in which no unit ran is refused.

def hundredths: . * 100 | round / 100;

# The package of a Cargo package id: the name before the version in its
# fragment, else the last segment of its source's path.
def package_name:
  (split("#") | last) as $fragment
  | if ($fragment | contains("@")) then $fragment | split("@") | first
    else split("#") | first | split("?") | first | split("/") | last end;

# A unit's name: its package, with its target unless it is the library.
def unit_name:
  (.package_id | package_name) as $package
  | (.target.kind | if type == "array" then first else . end) as $kind
  | if $kind == "lib" then $package
    elif .mode == "run-custom-build" then "\($package) (build script, run)"
    elif $kind == "build-script" then "\($package) (build script)"
    else "\($package) (\($kind))" end;

# A unit's directory under the workspace's root `$root`, or null.
def unit_source($root):
  ("path+file://\($root)/") as $prefix
  | if $root != null and (.package_id | startswith($prefix))
    then .package_id | ltrimstr($prefix) | split("#") | first
    else null end;

# The longest path through `$units` in the order `$order`, with the unit
# `$zero` at no time: one pass, since a dependency starts before each of its
# dependents.
def longest($units; $order; $zero):
  reduce $order[] as $i ({};
    . as $before
    | .[$i] = (if $i == $zero then 0 else $units[$i].duration end) + ([$units[$i].deps[] | $before[.]] | max // 0))
  | [.[]] | max // 0;

(map(select(.reason == "build-started") | .cwd) | first) as $root
| (reduce .[] as $record ({};
    ($record.index | tostring) as $i
    | if $record.reason == "unit-registered" then .[$i] += {name: ($record | unit_name), source: ($record | unit_source($root)), deps: (($record.dependencies // []) | map(tostring))}
      elif $record.reason == "unit-started" then .[$i].start = $record.elapsed
      elif $record.reason == "unit-rmeta-finished" then .[$i].meta = $record.elapsed
      elif $record.reason == "unit-section-started" and $record.section == "codegen" then .[$i].codegen = $record.elapsed
      elif $record.reason == "unit-finished" then .[$i].end = $record.elapsed
      else . end)
  | with_entries(select(.value.start != null and .value.end != null))
  | map_values(.duration = .end - .start))
  as $ran
| if ($ran | length) == 0 then error("the log records no unit that ran: build cold, with `-Zbuild-analysis`") else . end
| ($ran | map_values(.deps |= map(select($ran[.] != null)))) as $units
| ($units | to_entries | sort_by(.value.start, .value.end, .key) | map(.key)) as $order
| (reduce ($units | to_entries[]) as $e ({}; reduce $e.value.deps[] as $d (.; .[$d] += [$e.key]))) as $dependents
| (reduce $order[] as $i ({};
    . as $before
    | .[$i] = $units[$i].duration + ([$units[$i].deps[] | $before[.]] | max // 0)))
  as $to
| (reduce ($order | reverse)[] as $i ({};
    . as $after
    | .[$i] = $units[$i].duration + ([($dependents[$i] // [])[] | $after[.]] | max // 0)))
  as $from
| ($order | max_by($to[.])) as $last
| ([$last | recurse($units[.].deps | max_by($to[.]) // empty)] | reverse) as $path
| ($to[$last]) as $length
| ([range(0; $path | length) as $k
    | $units[$path[$k]] as $unit
    | ($path[$k + 1] // null) as $next
    | {unit: $unit.name,
       source: $unit.source,
       seconds: ($unit.duration | hundredths),
       front: (if $unit.codegen != null then $unit.codegen - $unit.start | hundredths else null end),
       bound: ($length - longest($units; $order; $path[$k]) | hundredths),
       waits: (if $next == null then null
               elif $unit.meta != null and $units[$next].start < $unit.end then "metadata"
               else "whole" end),
       counts: (if $next != null and $unit.meta != null and $units[$next].start < $unit.end then $unit.meta - $unit.start else $unit.duration end)}])
  as $chain
| ($units | map(.duration) | add) as $time
| ([$units[] | .end] | max) as $wall
| {units: ($units | length),
   wall: ($wall | hundredths),
   time: ($time | hundredths),
   in_flight: ($time / $wall | hundredths),
   longest: ($units | to_entries | max_by(.value.duration) | {unit: .value.name, seconds: (.value.duration | hundredths)}),
   length: ($length | hundredths),
   pipelined: ($chain | map(.counts) | add | hundredths),
   chain: ($chain | map(del(.counts))),
   off: ([$units | to_entries[] | select(.key as $k | $path | index($k) | not)]
     | sort_by(-.value.duration, .value.name)
     | .[:$top]
     | map({unit: .value.name, seconds: (.value.duration | hundredths), slack: ($length - ($to[.key] + $from[.key] - .value.duration) | hundredths)})),
   times: ([$units[]] | group_by(.name) | map({key: .[0].name, value: (map(.duration) | max | hundredths)}) | from_entries)}
