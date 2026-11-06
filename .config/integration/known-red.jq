# The known-red list of the integration cycle (#5440), read by `ci:cycle`.
# The input holds the verdict that `cycle.jq` gives, or null, the tip of
# `landing` that does not merge into `integration`, or null, whether the
# brake holds the landings (`brake.jq`), the run's JUnit reports as
# `yq -p xml` reads them, each under its lane, the names of the run's failed
# jobs, and the packages of the soundness suite (`soundness.json`).
#
# The output is the body of the one issue that holds the list, which each
# cycle rewrites, and whether the fixer gets a page. A test that fails in
# two lanes is one row. Each failed test of the soundness suite also gets an
# issue of its own: its title, its area and its body. The section
# `## The brake` stands in the body while the brake holds. Its text does not
# change with the lag, so a new lag alone does not rewrite the list.
def many: if . == null then [] elif type == "array" then . else [.] end;
def short: .[0:12];
def cell: tostring | gsub("\\|"; "\\|") | gsub("\n"; " ");
def collapsed($summary; $rows): "<details><summary>\($summary)</summary>\n\n\($rows | join("\n"))\n\n</details>";

. as $in
| [$in.reports[] | .lane as $lane
    | .junit.testsuites.testsuite | many | .[]
    | .testcase | many | .[]
    | select(has("failure") or has("error"))
    | {binary: .["+@classname"], test: .["+@name"], lane: $lane}]
| group_by([.binary, .test])
| map({binary: .[0].binary, test: .[0].test, lanes: (map(.lane) | unique)}) as $tests
| ($in.verdict != null and $in.verdict.conclusion != "success") as $red
| [$tests[] | (.binary | split("::")[0]) as $package
    | first($in.soundness[] | select(.package as $prefix | $package | startswith($prefix))) as $suite
    | {title: "soundness: \(.binary) \(.test) fails on integration",
       area: $suite.area,
       body: ("The test `\(.test)` of `\(.binary)` fails in the integration cycle on `\($in.verdict.sha | short)`. The test belongs to the soundness suite. Thus its failure is a defect of its own (#5440).\n\n"
         + "## Observation\n\n|Run|Commit|Lanes|\n|---|---|---|\n"
         + "|[\($in.verdict.id)](\($in.verdict.url))|`\($in.verdict.sha | short)`|\(.lanes | join(", "))|\n")}] as $soundness
| "The integration cycle keeps this list (#5440). Each cycle rewrites it. The fixer repairs each row on `integration` and never reverts a landing." as $lead
| (if $in.verdict == null then
      "No cycle has a verdict yet."
    elif $red | not then
      "The cycle on `\($in.verdict.sha | short)` passes: [run \($in.verdict.id)](\($in.verdict.url)). The list holds no test."
    else
      "The cycle on `\($in.verdict.sha | short)` fails: [run \($in.verdict.id)](\($in.verdict.url))."
    end) as $verdict
| (if $red | not then []
    elif $tests == [] then ["No test report names a failure. The failed jobs hold the cause."]
    else [collapsed("Known-red tests: \($tests | length), red";
      ["|Test|Binary|Lanes|", "|---|---|---|"] + [$tests[] | "|`\(.test | cell)`|`\(.binary | cell)`|\(.lanes | join(", ") | cell)|"])]
    end) as $list
| (if $red and $in.jobs != [] then
      [collapsed("Failed jobs: \($in.jobs | length)"; ["|Job|", "|---|"] + [$in.jobs[] | "|\(cell)|"])]
    else [] end) as $failed
| (if ($red | not) or $soundness == [] then []
    else ["The soundness suite holds \($soundness | length) of these tests. Each of them also has an issue of its own."] end) as $own
| (if $in.conflict == null then []
    else ["## The take\n\nThe tip of `landing`, `\($in.conflict | short)`, does not merge into `integration`. The fixer merges it on `integration` by hand."] end) as $take
| (if $in.brake == true then
      ["## The brake\n\nThe brake holds the landings (#5442). `main` lags `landing` past a limit of `.config/integration/brake.json`. A passing cycle moves `main`, and then the landings go on."]
    else [] end) as $brake
| {page: ($red or $in.conflict != null),
   body: ([$lead, $verdict] + $list + $own + $failed + $take + $brake | join("\n\n")),
   soundness: (if $red then $soundness else [] end)}
