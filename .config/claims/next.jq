# The claim order (#2533, `tracker.md` § tracker-claims): the next item a
# seat on a lane claims, as one `number<TAB>bucket<TAB>title` line, or none,
# after one `collector: #n (k open rows)` line for each collector in the
# lane's areas that is no defect and holds an open row (#3111, #3326), one
# `blocked: #n` line for each issue ranked ahead of it that waits on an open
# issue, one `observation due: #n — <command>` line when the pick is a defect
# (#3758), one `sections due: #n — <finding>` line for each section the pick
# lacks (#3134), and one `restate: `<axis>`: <question>` line for each of the
# pick's readings still the migration's `unstated` placeholder (#2955).
#
# Input:
#   areas    the lane's area labels, `area:<name>`, in the lane's order
#            (`.config/issues/lanes.toml`, #3736)
#   issues   the open issues: [{number, title, labels: [name], parent, body,
#            blocked}], parent the number of the issue's parent, or null; body
#            the issue's body, or null; blocked how many open issues it is
#            GitHub-`blocked by` (#2902), or null for none, as the board
#            reads it
#   live     the open issues each issue it names is GitHub-`blocked by`,
#            read from the issue now: {"<n>": [number]}; absent reads as
#            none. It outranks `blocked`, which lags a dependency set or
#            removed (#4104)
#   order    each open epic's sub-issues in the epic's order: {"<epic>": [number]}
#   refusals the refusals `.config/debug/refusals.toml` names; absent reads
#            as none
#   lane     the lane claiming, a key of `.config/issues/lanes.toml`; absent,
#            the board is read for no lane, and neither rule below applies
#   now      the reading's time, in seconds since the epoch
#   prs      the open pull requests: [{body, head}]
#   focus    the programme focus (`.config/issues/focus.toml`, #3959), or
#            absent for none: {epics: [number], members: [{number, epic}],
#            landings: [{number, body, head}]}, members every sub-issue of a
#            focus epic in any state, a sub-epic's in turn, each with the
#            focus epic it falls under; landings the merged pull requests the
#            open issues' `from:` lines name
#
# An issue is a candidate when it is unowned (no `status:claimed`), not ruled
# out (`status:deferred`, `status:discarded`) and not an epic. A `collector`
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
# holds a claimed issue when its claim marker names the lane (`markers.jq`),
# or, with no marker, when the issue is in the lane's areas, as a stall
# reading places it. A lane holding a claimed issue that no open pull request
# names (`names`, as the lifecycle reads it) claims nothing: the answer is one
# `held: #n <title>` line per such issue and no pick, and `claim:release` is
# the way out. An issue a lane released, or a merge on its branch advanced,
# in the last 2 hours comes first for that lane, ahead of every bucket, the
# latest release first, and no other lane claims it in those 2 hours: the
# continuation stays with the lane that holds its context.
#
# A focus narrows the order to the programme's work (#3959): the answer opens
# with `focus: #<epic> …`, and the order offers nothing outside the focus, a
# release or a collector included. First a `kind:defect` or `kind:refactor`
# in the focus: its parent, or any `#n` its body writes, names a member or a
# focus epic, or a `from:` line names a landing that works a member (`names`).
# These rank by priority, effort and age, the lane's areas first, then any
# area. Then a member, the focus units, in the focus epics' order and each
# epic's sub-issue order, by priority first, the lane's areas first, then any
# area. A member waits while a sub-epic between it and its focus epic carries
# `status:deferred` (#4063), as the plain order passes over a deferred epic's
# units. A lane still holds what it holds, the focus aside.

include "sections";
include "findings";
include "targets";
include "markers";

def has($label): .labels | index($label) != null;
def within($areas): .labels as $labels | any($areas[]; . as $area | $labels | index($area) != null);
def unruled:
  (has("status:claimed") or has("status:deferred") or has("status:discarded") or has("kind:epic")) | not;
def candidate: unruled and (has("collector") | not);
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

# A release within the 2 hours a lane keeps its continuation (#3915).
def kept($now): .body | release | select(. != null and $now - .at < 7200);
# Whether lane `$lane`, over `$areas`, holds this claimed issue.
def held_by($lane; $areas): (.body | claim_lane) as $marked | if $marked != null then $marked == $lane else within($areas) end;

# A collector's open rows (#3111), as `collector_rows` reads them.
def open_rows: .body // "" | collector_rows | length;

# The command a defect's observation starts from (#3758): the refusal its
# title names, a table of `.config/debug/refusals.toml`, else the test alone.
def observation($refusals):
  .title as $title
  | ([$refusals[] | select(. as $name | $title | test("\\b\($name)\\b"))] | first) as $refusal
  | "observation due: #\(.number) — mise run "
    + (if $refusal == null then "debug:test <package> <test>" else "debug:refusal \($refusal) <package> <test>" end);

.areas as $areas
| .order as $order
| (.refusals // []) as $refusals
| .lane as $lane
| (.now // 0) as $now
| (.live // {}) as $live
| (.prs // []) as $prs
| [.issues[] | select(has("kind:epic") and (has("status:deferred") | not)) | .number] as $epics
| (if .focus == null or (.focus.epics | length) == 0 then null
   else .focus as $focus
     | {epics: $focus.epics, members: $focus.members,
        named: ($focus.epics + [$focus.members[].number]),
        landings: [$focus.landings[] | . as $pr | select(any($focus.members[]; . as $m | $pr | names($m.number))) | .number]}
   end) as $focus
| def written: [.body // "" | scan("(?<![\\w/])#([0-9]+)\\b") | .[0] | tonumber];
  def focus_fix:
    (has("kind:defect") or has("kind:refactor"))
    and ((.parent | IN($focus.named[])) or any(written[]; IN($focus.named[]))
      or any(.body // "" | from_lines[]; IN($focus.landings[])));
  def membership: .number as $n | first($focus.members[] | select(.number == $n)) // null;
  # Whether a member's chain of parents up to its focus epic meets a deferred
  # sub-epic.
  def waits: .parent as $p | first($focus.members[] | select(.number == $p)) // null
    | if . == null then false
      elif (.labels // [] | index("status:deferred")) != null then true
      else waits end;
  def focus_unit: membership as $m | $m != null and ($m | waits | not) and (focus_fix | not);
  def focus_rank: membership as $m
    | [($focus.epics | index($m.epic)), (.number as $n | $order["\(.parent)"] // [] | index($n) // infinite)];
  def fixed: [., if has("kind:defect") then "defect" else "refactor" end];
  (if $focus == null then empty else "focus: \($focus.epics | map("#\(.)") | join(" "))" end),
  (.
| (if $lane == null then []
   else [.issues[] | select(has("status:claimed") and held_by($lane; $areas))
     | . as $issue | select([$prs[] | names($issue.number)] | any | not)]
   end) as $held
| if ($held | length) > 0 then $held[] | "held: #\(.number) \(.title)" else
  [.issues[] | select(candidate) | select($lane == null or ([kept($now) | .lane != $lane] | any | not))] as $open
| if $focus != null then [
    ($open | map(select([kept($now) | .lane == $lane] | any) | select(focus_fix or focus_unit)) | sort_by(-(kept($now) | .at), .number) | .[] | [., "released"]),
    ($open | map(select(focus_fix and within($areas))) | sort_by(priority, effort, .number) | .[] | fixed),
    ($open | map(select(focus_fix and (within($areas) | not))) | sort_by(priority, effort, .number) | .[] | fixed),
    ($open | map(select(focus_unit and within($areas))) | sort_by(priority, focus_rank, .number) | .[] | [., "focus"]),
    ($open | map(select(focus_unit and (within($areas) | not))) | sort_by(priority, focus_rank, .number) | .[] | [., "focus"])
  ] else [
    ($open | map(select([kept($now) | .lane == $lane] | any)) | sort_by(-(kept($now) | .at), .number) | .[] | [., "released"]),
    (.issues
      | map(select(has("collector") and has("kind:defect") and within($areas) and unruled and open_rows > 0))
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
  ] end as $ranked
| ([.issues[] | select(has("collector") and within($areas) and (has("kind:defect") | not))]
    | sort_by(.number) | .[] | open_rows as $k | select($k > 0)
    | "collector: #\(.number) (\($k) open row\(if $k == 1 then "" else "s" end))"),
  ([range(0; $ranked | length) | select($ranked[.][0] | blocked($live) | not)] | first) as $at
| ($ranked[:$at // ($ranked | length)]
    | reduce .[] as $entry ([]; if any(.[]; .number == $entry[0].number) then . else . + [$entry[0]] end)
    | .[] | "blocked: #\(.number)"),
  ($at // empty | $ranked[.]
    | (select(.[0] | has("kind:defect")) | .[0] | observation($refusals)),
      (select(.[1] != "collector") | .[0] | .number as $n | .body // "" | findings | "sections due: #\($n) — \(.)"),
      (select(.[1] != "collector") | .[0] | quoted(unstated_axes)[] | "restate: \(.)"),
      "\(.[0].number)\t\(.[1])\t\(.[0].title)")
  end
  )
