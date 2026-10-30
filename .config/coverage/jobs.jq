# The coverage workflow's measure (#4020). The whole instrumented run in one
# job reached the job's 45-minute limit, so a job that runs `ci:coverage`
# runs one part of it, named by `COVERAGE_PART` from its matrix. Every
# matrix entry names its part, and the parts together are the whole: each
# nextest slice `hash:<k>/<n>` for k from 1 to n once, and `plain` once.
#
# Input: `.github/workflows/coverage.yml`'s `jobs`, anchors expanded, as JSON.
# Output: the refusals, a JSON array of lines, empty when the jobs hold.

def measures: (.steps // []) | any((.run // "") | test("\\bci:coverage(\\s|$)"));

[to_entries[]
  | select(.key != "template" and (.value | measures))
  | .key as $job
  | .value as $value
  | ($value.strategy.matrix.include // []) as $entries
  | ($entries | map(.slice)) as $slices
  | ($slices | map(select(. != null) | capture("^hash:(?<k>[0-9]+)/(?<n>[0-9]+)$") | {k: (.k | tonumber), n: (.n | tonumber)})) as $hashes
  | ($hashes | map(.n) | unique) as $counts
  | if ($value.env.COVERAGE_PART // null) == null or ($entries | length) == 0
    then "`\($job)` runs the whole instrumented suite in one job, which reached its 45-minute limit: run one part a job, `ci:coverage \"$COVERAGE_PART\"` with the part from the job's matrix (#4020)"
    else
      ($entries[] | select(.slice == null) | "`\($job)` has a matrix entry `\(.part // "unnamed")` naming no `slice`: name its part, `hash:<k>/<n>` or `plain` (#4020)"),
      (if ($slices | map(select(. == "plain")) | length) != 1
       then "`\($job)` runs the plain-only witness \($slices | map(select(. == "plain")) | length) times: run it once, as the part `plain` (#4020)"
       else empty end),
      (if ($counts | length) != 1
       then "`\($job)` runs the enforcing suite in slices of \(if ($counts | length) == 0 then "no count" else ($counts | map(tostring) | join(" and ")) end): name one count n and every slice `hash:1/n` to `hash:n/n` once (#4020)"
       elif ($hashes | map(.k) | sort) != [range(1; $counts[0] + 1)]
       then "`\($job)` runs the slices \($hashes | map(.k) | sort | map(tostring) | join(", ")) of \($counts[0]): run every slice `hash:1/\($counts[0])` to `hash:\($counts[0])/\($counts[0])` once (#4020)"
       else empty end)
    end]
