# The claim order (#2533, `tracker.md` § tracker-claims): the next item a
# seat on an area claims, as one `number<TAB>bucket<TAB>title` line, or none,
# after one `collector: #n (k open rows)` line for each collector in the
# area that is no defect and holds an open row (#3111, #3326), one
# `blocked: #n` line for each issue ranked ahead of it that waits on an open
# issue, one `sections due: #n — <finding>` line for each section the pick
# lacks (#3134), and one `restate: `<axis>`: <question>` line for each of the
# pick's readings still the migration's `unstated` placeholder (#2955).
#
# Input:
#   area     the area's label, `area:<name>`
#   issues   the open issues: [{number, title, labels: [name], parent, body,
#            blocked}], parent the number of the issue's parent, or null; body
#            the issue's body, or null; blocked how many open issues it is
#            GitHub-`blocked by` (#2902), or null for none
#   order    each open epic's sub-issues in the epic's order: {"<epic>": [number]}
#
# An issue is a candidate when it is unowned (no `status:claimed`), not ruled
# out (`status:deferred`, `status:discarded`) and not an epic. A `collector`
# is a candidate only as a `kind:defect` in the area holding an open row
# (#3326): it heads the order, ahead of every other bucket, and is claimed and
# worked as the defect it is. Its rows carry no dates, so the oldest
# collector, the lowest number, comes first. Any other collector in the area
# holding an open row is printed with its open rows, so the carving due is
# seen (#3111); a collector with no open row is neither picked nor printed.
# The buckets after it, in order: a `kind:defect` in the area; a
# `kind:refactor` in the area, the refactoring a landing's `## Refactoring`
# verdict asked for (#2884); a `kind:performance` in the area, then any
# `kind:performance`; a `kind:gap` in the area; then a planned unit, an issue
# in the area whose parent is an open epic not itself deferred, the oldest
# epic first and its sub-issues in the epic's order. A defect in another area
# is not offered: its `area:` is its route to a seat, and one no seat holds is
# the coordinator's to relabel (#3111). Within each bucket the `priority:`
# label ranks first (`high`, `medium`, `backlog`, then none, #2902), so
# defects stay first across buckets and a high one leads its own. Defects and
# gaps then rank by `effort:`, cheapest first (`easy`, `medium`, `hard`,
# `unknown`, then none): every defect is high by default, so effort is what
# separates them (#3111). Then the oldest issue comes first. The pick is the
# first candidate no open issue blocks (#2902), sectioned or not: the seat
# that claims an issue has its context, so sectioning is the claim's first
# obligation (#3134, reversing #2744's pass-over and #3112's coordinator
# lines). Each section it lacks (`findings.jq`, as `unit:check` reads it) is
# printed as `sections due`; the seat writes them, runs `## Try first` before
# `## The shape` is final, and pages the coordinator for `shape:signed`,
# without which `pr:open` refuses the landing (`opening.jq`). A collector
# keeps its own shape, so a collector pick prints no section due and no
# reading to restate. Each candidate ranked ahead of the pick that an open
# issue blocks is named once, so the seat sees why it was passed over. A pick
# whose reading is the `unstated` placeholder is claimed all the same, its
# axes' questions printed first.

include "sections";
include "findings";

def has($label): .labels | index($label) != null;
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
def blocked: (.blocked // 0) > 0;

# A collector's open rows (#3111), as `collector_rows` reads them.
def open_rows: .body // "" | collector_rows | length;

.area as $area
| .order as $order
| [.issues[] | select(has("kind:epic") and (has("status:deferred") | not)) | .number] as $epics
| [.issues[] | select(candidate)] as $open
| [
    (.issues
      | map(select(has("collector") and has("kind:defect") and has($area) and unruled and open_rows > 0))
      | sort_by(.number) | .[] | [., "collector"]),
    ($open | map(select(has("kind:defect") and has($area))) | sort_by(priority, effort, .number) | .[] | [., "defect"]),
    ($open | map(select(has("kind:refactor") and has($area))) | sort_by(priority, .number) | .[] | [., "refactor"]),
    ($open | map(select(has("kind:performance") and has($area))) | sort_by(priority, .number) | .[] | [., "performance"]),
    ($open | map(select(has("kind:performance"))) | sort_by(priority, .number) | .[] | [., "performance"]),
    ($open | map(select(has("kind:gap") and has($area))) | sort_by(priority, effort, .number) | .[] | [., "gap"]),
    ($open
      | map(select(has($area) and .parent != null) | .parent as $p | select($epics | index($p) != null))
      | sort_by(priority, .parent, (.number as $n | $order["\(.parent)"] // [] | index($n) // infinite), .number)
      | .[] | [., "planned"])
  ] as $ranked
| ([.issues[] | select(has("collector") and has($area) and (has("kind:defect") | not))]
    | sort_by(.number) | .[] | open_rows as $k | select($k > 0)
    | "collector: #\(.number) (\($k) open row\(if $k == 1 then "" else "s" end))"),
  ([range(0; $ranked | length) | select($ranked[.][0] | blocked | not)] | first) as $at
| ($ranked[:$at // ($ranked | length)]
    | reduce .[] as $entry ([]; if any(.[]; .number == $entry[0].number) then . else . + [$entry[0]] end)
    | .[] | "blocked: #\(.number)"),
  ($at // empty | $ranked[.]
    | (select(.[1] != "collector") | .[0] | .number as $n | .body // "" | findings | "sections due: #\($n) — \(.)"),
      (select(.[1] != "collector") | .[0] | quoted(unstated_axes)[] | "restate: \(.)"),
      "\(.[0].number)\t\(.[1])\t\(.[0].title)")
