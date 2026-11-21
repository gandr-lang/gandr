# What one CI run's test times do to the slow-test collectors (#3752). A
# test past its budget is marked slow by nextest and runs on: only a test
# past five minutes fails the run (`.config/nextest.toml`, `[profile.ci]`).
# So a slow test never dequeues a pull request; it files one `collector` per
# test, `test: <binary> <test> ran <t> s in the <lane> lane, past its <b> s
# budget`, one row per run.
#
# A run past the budget adds an open row, `- [ ] [run <id>](<url>) — <lane>:
# <t> s`, to the test's open collector, or opens one, and the title takes the
# run's time and lane. A run that times the test under the budget adds a
# ticked row to its open collector, and three ticked rows in a row close it.
# A run that does not time the test changes nothing: a lane or a shard that
# did not run says nothing of it. A row for the run already present adds
# nothing, so a run read twice files once.
#
# A collector is its budget's: only an issue whose title ends `past its <b> s
# budget` is read, so a sweep's 30 s collector from the merge queue and its
# 240 s one from the nightly (#3975) stay apart.
#
# Input:
#   budget   the budget in seconds
#   reason   what the run did with a test past the budget, the body's
#            sentence after `ran past its <b> s budget`; absent, the merge
#            queue's: nextest marks it slow and runs it on
#   run      {id, url}: the run whose reports were read
#   times    [{lane, binary, test, seconds}]: each test once, in the lane it
#            held longest (`test-timing --times`)
#   issues   the open slow-test collectors: [{number, title, body}]
#
# Output: one {number, title, body, close, line} per collector to open
# (`number` null), update or close; `line` is the run summary's line.

def hundredths: . * 100 | round / 100;
def lane_name: sub("^junit-"; "");
def runs: [(.body // "") | split("\n")[] | select(test("^- \\[[ x]\\] \\[run [0-9]+\\]"))];
def held($id): any(.[]; contains("[run \($id)]"));
def closes: length >= 3 and (.[-3:] | all(startswith("- [x]")));

. as $in
| def row($ticked; $time):
    "- [\(if $ticked then "x" else " " end)] [run \($in.run.id)](\($in.run.url)) — `\($time.lane | lane_name)`: \($time.seconds | hundredths) s"
    + (if $ticked then ", under budget" else "" end);
  def title($time):
    "test: \($time.binary) \($time.test) ran \($time.seconds | hundredths) s in the \($time.lane | lane_name) lane, past its \($in.budget) s budget";
  def body($binary; $test; $rows):
    "`\($test)` in `\($binary)` ran past its \($in.budget) s budget "
    + ($in.reason // "in CI. nextest marks such a test slow and runs it on, so it never dequeues a pull request. Only a test past 5 minutes fails the run (#3752).")
    + "\n\n"
    + "Each run that times the test adds a row. A run under the budget ticks its row, and three ticked rows in a row close this collector.\n\n"
    + "## Runs\n\n" + ($rows | join("\n")) + "\n";
  [$in.issues[] | select(.title | endswith("past its \($in.budget) s budget")) | . + (.title | capture("^test: (?<binary>\\S+) (?<test>\\S+) ran "))] as $open
| ($in.times | map({key: "\(.binary)\t\(.test)", value: .}) | from_entries) as $timed
| [$in.times[]
    | select(.seconds > $in.budget)
    | . as $time
    | ([$open[] | select(.binary == $time.binary and .test == $time.test)] | first) as $issue
    | (if $issue == null then [] else ($issue | runs) end) as $rows
    | select($rows | held($in.run.id) | not)
    | {number: $issue.number,
       title: title($time),
       body: body($time.binary; $time.test; $rows + [row(false; $time)]),
       close: false,
       line: "- `\($time.test)` in `\($time.binary)`: \($time.seconds | hundredths) s in `\($time.lane | lane_name)`, past its \($in.budget) s budget"}]
  + [$open[]
    | $timed["\(.binary)\t\(.test)"] as $time
    | select($time != null and $time.seconds <= $in.budget)
    | runs as $rows
    | select($rows | held($in.run.id) | not)
    | ($rows + [row(true; $time)]) as $next
    | {number,
       title,
       body: body(.binary; .test; $next),
       close: ($next | closes),
       line: "- `\(.test)` in `\(.binary)`: \($time.seconds | hundredths) s in `\($time.lane | lane_name)`, under budget"}]
