# The claim order (#2533, `tracker.md` § tracker-claims): the next item a
# seat on a lane claims, as one `number<TAB>bucket<TAB>title` line, or none,
# after one `unattributed: #n <title>` line for each claim in the lane's
# areas that names no lane (#4504), one `collector: #n (k open rows)` line
# for each collector in the lane's areas that is no defect and holds an open
# row (#3111, #3326), one `blocked: #n` line for each issue ranked ahead of
# it that waits on an open issue, one `observation due: #n — <command>` line
# when the pick is a defect (#3758), one `sections due: #n — <finding>` line
# for each section the pick lacks (#3134), and one `restate: `<axis>`:
# <question>` line for each of the pick's readings still the migration's
# `unstated` placeholder (#2955).
#
# Input:
#   areas    the lane's area labels, `area:<name>`, in the lane's order
#            (the factory's lane table, #3736)
#   issues   the open issues: [{number, title, labels: [name], parent, body,
#            blocked}], parent the number of the issue's parent, or null; body
#            the issue's body, or null; blocked how many open issues it is
#            GitHub-`blocked by` (#2902), or null for none, as the board
#            reads it
#   live     the open issues each issue it names is GitHub-`blocked by`,
#            read from the issue now: {"<n>": [number]}; absent reads as
#            none. It outranks `blocked`, which lags a dependency set or
#            removed (#4104)
#   reread   issues read from GitHub again just before the claim: {"<n>":
#            {labels: [name], body}}; absent reads as none. A reading here
#            outranks the board's, which is as old as the run (#4660)
#   order    each open epic's sub-issues in the epic's order: {"<epic>": [number]}
#   refusals the refusals `.config/debug/refusals.toml` names; absent reads
#            as none
#   lane     the lane claiming, a key of the factory's lane table; absent,
#            the board is read for no lane, and neither rule below applies
#   now      the reading's time, in seconds since the epoch
#   prs      the open pull requests: [{body, head}]
#   lanes    the keys of the factory's lane table; absent reads as none
#   branches origin's branches working a claimed issue with no claim marker:
#            [{head, at}], at the head commit's time in seconds since the
#            epoch; absent reads as none (#3951)
#
# An issue is a candidate when it is unowned (no `status:claimed`, and no
# other lane's claim marker, #4660), not ruled
# out (`status:deferred`, `status:discarded`) and not an epic. An issue an open
# pull request `names` is worked though no label claims it, so it is no
# candidate for any lane, whatever the pull request's base (#4650). A `collector`
# is a candidate only as a `kind:defect` in a lane's area holding an open row
# (#3326): it heads the order, ahead of every other bucket, and is claimed and
# worked as the defect it is. Its rows carry no dates, so the oldest
# collector, the lowest number, comes first. Any other collector in the
# lane's areas holding an open row is printed with its open rows, so the
# carving due is seen (#3111); a collector with no open row is neither picked
# nor printed. The buckets after it, in order: a `kind:defect` in the lane's
# areas; a `kind:refactor` in them, the refactoring a landing's
# `## Refactoring` verdict asked for (#2884); then a `kind:defect` or a
# `kind:refactor` in any area, the oldest first, so a bucket no lane asks for
# drains before planned work (#3736, reversing #3111's rule that a defect in
# another area is not offered); a `kind:performance` in the lane's areas; a
# `kind:gap` in the lane's areas; then a planned unit, an issue in the lane's
# areas whose parent is an open epic not itself deferred, the oldest epic
# first and its sub-issues in the epic's order; and last a `kind:performance`
# or a `kind:gap` in any area, another lane's planned work, which a lane takes
# only once its own is done (#3827). Within each bucket of the lane the
# `priority:` label ranks first
# (`high`, `medium`, `backlog`, then none, #2902), so defects stay first
# across buckets and a high one leads its own. Defects and gaps then rank by
# `effort:`, cheapest first (`easy`, `medium`, `hard`, `unknown`, then none):
# every defect is high by default, so effort is what separates them (#3111).
# Then the oldest issue comes first. The pick is the
# first candidate no open issue blocks (#2902), sectioned or not: the seat
# that claims an issue has its context, so sectioning is the claim's first
# obligation (#3134, reversing #2744's pass-over and #3112's coordinator
# lines). Each section it lacks (`findings.jq`, as `unit:check` reads it) is
# printed as `sections due`; the seat writes them, runs `## Try first` before
# `## The shape` is final, and pages the coordinator for `shape:signed`,
# without which `pr:open` refuses the landing (`opening.jq`). A collector
# keeps its own shape, so a collector pick prints no section due and no
# reading to restate. Each candidate ranked ahead of the pick that an open
# issue blocks is named once, so the seat sees why it was passed over. An
# issue `live` names is blocked by the open issues it lists there alone. A
# pick whose reading is the `unstated` placeholder is claimed all the same,
# its axes' questions printed first.
#
# A claim is the slice in hand (`tracker.md` § tracker-claims, #3915). A lane
# holds a claimed issue when its claim marker names the lane (`markers.jq`).
# With no marker, the lane whose branch on origin works the issue holds it
# (#3951): `<lane>-<n>-<slug>` or `<lane>-<seat>-<n>-<slug>`, the lane the
# longest `lanes` key the branch opens with, the newest head first when two
# lanes' branches work it. With neither, the claim names no lane (#4504): no
# lane holds it, and each lane over one of its areas prints one
# `unattributed: #n <title>` line for it before its answer. A claimed issue a
# lane holds that no open pull request names (`names`, as the lifecycle reads
# it) prints one `held: #n <title>` line, and the lane claims its next unit
# all the same: a lane never waits on its own unopened work, and the claim
# window releases a claim nobody works (`claim:release`). An issue a lane
# released, or a merge on its branch advanced, in the last 2 hours comes
# first for that lane, ahead of every bucket, the latest release first, and
# no other lane claims it in those 2 hours: the continuation stays with the
# lane that holds its context.

include "sections";
include "findings";
include "targets";
include "markers";

def has($label): .labels | index($label) != null;
def within($areas): .labels as $labels | any($areas[]; . as $area | $labels | index($area) != null);
def unruled:
  (has("status:claimed") or has("status:deferred") or has("status:discarded") or has("kind:epic")) | not;
def candidate: unruled and (has("collector") | not);
# Whether no other lane's claim marker stands in the body (#4660): a run that
# read the board before another lane's claim landed sees it on the reread.
def unclaimed($lane): ((.body | claim_lane) // $lane) == $lane;
def effort:
  ["effort:easy", "effort:medium", "effort:hard", "effort:unknown"] as $ranks
  | [.labels[] as $l | $ranks | index($l) | values] | min // 4;
def priority:
  ["priority:high", "priority:medium", "priority:backlog"] as $ranks
  | [.labels[] as $l | $ranks | index($l) | values] | min // 3;
def unstated_axes: [.body // "" | marks | select(.reason | unstated) | .axis];
def quoted($marked): [axes[] | . as $axis | select($marked | index($axis)) | "`\($axis)`: \(questions[$axis])"];
def blocked($live): $live["\(.number)"] as $read
  | if $read != null then $read | length > 0 else (.blocked // 0) > 0 end;

# The lane a branch names: the longest key of `$lanes` the branch is, or
# opens with before a `-`, or null.
def branch_lane($lanes):
  . as $head | [$lanes[] | select(. as $lane | $head == $lane or ($head | startswith($lane + "-")))] | max_by(length);
# Whether a branch works issue `$n`: after its lane, `<n>-<slug>` or a numbered
# seat's `<seat>-<n>-<slug>`, the forms `opening.jq` reads.
def works($n; $lanes):
  branch_lane($lanes) as $lane
  | $lane != null and (.[($lane | length) + 1:] | test("^([0-9]+-)?\($n)(-[a-z]|$)"));
# The lane whose branch on origin works this issue, the newest head first, or
# null.
def worked_by($branches; $lanes):
  .number as $n | [$branches[] | select(.head | works($n; $lanes))] | max_by(.at) // null
  | if . == null then null else .head | branch_lane($lanes) end;
# The lane that holds this claimed issue: the lane its marker names, else the
# lane whose branch works it (#3951), else null. A claim with neither names no
# lane, and no lane's areas take it (#4504).
def placed($branches; $lanes):
  ((.body | claim_lane) // worked_by($branches; $lanes)) as $placed | $placed;

# A collector's open rows (#3111), as `collector_rows` reads them.
def open_rows: .body // "" | collector_rows | length;

# The command a defect's observation starts from (#3758): the refusal its
# title names, a table of `.config/debug/refusals.toml`, else the test alone.
def observation($refusals):
  .title as $title
  | ([$refusals[] | select(. as $name | $title | test("\\b\($name)\\b"))] | first) as $refusal
  | "observation due: #\(.number) — mise run "
    + (if $refusal == null then "debug:test <package> <test>" else "debug:refusal \($refusal) <package> <test>" end);

(.reread // {}) as $reread
| .issues |= map(. + ($reread["\(.number)"] // {}))
| .areas as $areas
| .order as $order
| (.refusals // []) as $refusals
| .lane as $lane
| (.now // 0) as $now
| (.live // {}) as $live
| (.prs // []) as $prs
| (.branches // []) as $branches
| (.lanes // []) as $lanes
| [.issues[] | select(has("kind:epic") and (has("status:deferred") | not)) | .number] as $epics
| def fixed: [., if has("kind:defect") then "defect" else "refactor" end];
  (if $lane == null then empty
   else .issues[] | select(has("status:claimed") and placed($branches; $lanes) == null and within($areas))
     | "unattributed: #\(.number) \(.title)"
   end),
  (.
| (if $lane == null then []
   else [.issues[] | select(has("status:claimed") and placed($branches; $lanes) == $lane)
     | . as $issue | select([$prs[] | names($issue.number)] | any | not)]
   end) as $held
| ($held[] | "held: #\(.number) \(.title)"), (
  [.issues[] | select(candidate and unclaimed($lane)) | . as $issue | select([$prs[] | names($issue.number)] | any | not)
    | select($lane == null or ([.body | kept($now) | .lane != $lane] | any | not))] as $open
| [
    ($open | map(select([.body | kept($now) | .lane == $lane] | any)) | sort_by(-(.body | kept($now) | .at), .number) | .[] | [., "released"]),
    (.issues
      | map(select(has("collector") and has("kind:defect") and within($areas) and unruled and unclaimed($lane) and open_rows > 0))
      | sort_by(.number) | .[] | [., "collector"]),
    ($open | map(select(has("kind:defect") and within($areas))) | sort_by(priority, effort, .number) | .[] | [., "defect"]),
    ($open | map(select(has("kind:refactor") and within($areas))) | sort_by(priority, .number) | .[] | [., "refactor"]),
    ($open | map(select(has("kind:defect") or has("kind:refactor"))) | sort_by(.number) | .[] | [., if has("kind:defect") then "defect" else "refactor" end]),
    ($open | map(select(has("kind:performance") and within($areas))) | sort_by(priority, .number) | .[] | [., "performance"]),
    ($open | map(select(has("kind:gap") and within($areas))) | sort_by(priority, effort, .number) | .[] | [., "gap"]),
    ($open
      | map(select(within($areas) and .parent != null) | .parent as $p | select($epics | index($p) != null))
      | sort_by(priority, .parent, (.number as $n | $order["\(.parent)"] // [] | index($n) // infinite), .number)
      | .[] | [., "planned"]),
    ($open | map(select(has("kind:performance"))) | sort_by(priority, .number) | .[] | [., "performance"]),
    ($open | map(select(has("kind:gap"))) | sort_by(priority, effort, .number) | .[] | [., "gap"])
  ] as $ranked
| ([.issues[] | select(has("collector") and within($areas) and (has("kind:defect") | not))]
    | sort_by(.number) | .[] | open_rows as $k | select($k > 0)
    | "collector: #\(.number) (\($k) open row\(if $k == 1 then "" else "s" end))"),
  ([range(0; $ranked | length) | select($ranked[.][0] | blocked($live) | not)] | first) as $at
| ($ranked[:$at // ($ranked | length)]
    | reduce .[] as $entry ([]; if any(.[]; .number == $entry[0].number) then . else . + [$entry[0]] end)
    | .[] | "blocked: #\(.number)"),
  ($at // empty | $ranked[.]
    | (select(.[0] | has("kind:defect")) | .[0] | observation($refusals)),
      (select(.[1] != "collector") | .[0] | .number as $n | .labels as $labels | .body // "" | findings($labels; $n) | "sections due: #\($n) — \(.)"),
      (select(.[1] != "collector") | .[0] | quoted(unstated_axes)[] | "restate: \(.)"),
      "\(.[0].number)\t\(.[1])\t\(.[0].title)")
  )
  )
