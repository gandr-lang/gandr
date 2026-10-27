# The claim order (#2533, `tracker.md` § tracker-claims): the next item a
# seat on an area claims, as one `number<TAB>bucket<TAB>title` line, or none,
# after one `needs sections: #n` or `blocked: #n` line for each issue ranked
# ahead of it that lacks a unit's sections or waits on an open issue, and one
# `restate: `<axis>`: <question>` line for each of the pick's readings still
# the migration's `unstated` placeholder (#2955).
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
# out (`status:deferred`, `status:discarded`), not an epic and not a
# `collector`, whose rows a guard keeps and other issues work (#2621). The
# buckets, in order: a `kind:defect` in the area, then any `kind:defect`; a
# `kind:refactor` in the area, the refactoring a landing's `## Refactoring`
# verdict asked for (#2884); a `kind:performance` in the area, then any
# `kind:performance`; a `kind:gap` in
# the area, cheapest first by its `effort:` label (`easy`, `medium`, `hard`,
# `unknown`, then none); then a planned unit, an issue in the area whose
# parent is an open epic not itself deferred, the oldest epic first and its
# sub-issues in the epic's order. Within each bucket the `priority:` label
# ranks first (`high`, `medium`, `backlog`, then none, #2902), so defects
# stay first across buckets and a high one leads its own; then the oldest
# issue comes first. The pick is the first candidate `unit:check` passes
# (`findings.jq`, #2744) and no open issue blocks (#2902); each one ranked
# ahead of it that fails either is named once, as blocked when it is, so the
# coordinator sees whose sections to write and the seat why it was passed
# over. A `needs sections:` line quotes the question of each axis whose
# reading is bare. A pick whose reading is the `unstated` placeholder is
# claimed all the same, its axes' questions printed first: the seat restates
# those rows on the issue as its first act, and `pr:open` refuses the landing
# until it has (`opening.jq`).

include "sections";
include "findings";

def has($label): .labels | index($label) != null;
def candidate:
  (has("status:claimed") or has("status:deferred") or has("status:discarded") or has("kind:epic")
    or has("collector")) | not;
def effort:
  ["effort:easy", "effort:medium", "effort:hard", "effort:unknown"] as $ranks
  | [.labels[] as $l | $ranks | index($l) | values] | min // 4;
def priority:
  ["priority:high", "priority:medium", "priority:backlog"] as $ranks
  | [.labels[] as $l | $ranks | index($l) | values] | min // 3;
def bare: [.body // "" | marks | select(.mark != null and .reason == null) | .axis];
def unstated_axes: [.body // "" | marks | select(.reason | unstated) | .axis];
def ready: [.body // "" | findings] | length == 0;
def quoted($marked): [axes[] | . as $axis | select($marked | index($axis)) | "`\($axis)`: \(questions[$axis])"];
def needs:
  quoted(bare) as $axes
  | "needs sections: #\(.number)" + (if ($axes | length) > 0 then " — restate " + ($axes | join(" · ")) else "" end);
def blocked: (.blocked // 0) > 0;

.area as $area
| .order as $order
| [.issues[] | select(has("kind:epic") and (has("status:deferred") | not)) | .number] as $epics
| [.issues[] | select(candidate)] as $open
| [
    ($open | map(select(has("kind:defect") and has($area))) | sort_by(priority, .number) | .[] | [., "defect"]),
    ($open | map(select(has("kind:defect"))) | sort_by(priority, .number) | .[] | [., "defect"]),
    ($open | map(select(has("kind:refactor") and has($area))) | sort_by(priority, .number) | .[] | [., "refactor"]),
    ($open | map(select(has("kind:performance") and has($area))) | sort_by(priority, .number) | .[] | [., "performance"]),
    ($open | map(select(has("kind:performance"))) | sort_by(priority, .number) | .[] | [., "performance"]),
    ($open | map(select(has("kind:gap") and has($area))) | sort_by(priority, effort, .number) | .[] | [., "gap"]),
    ($open
      | map(select(has($area) and .parent != null) | .parent as $p | select($epics | index($p) != null))
      | sort_by(priority, .parent, (.number as $n | $order["\(.parent)"] // [] | index($n) // infinite), .number)
      | .[] | [., "planned"])
  ] as $ranked
| ([range(0; $ranked | length) | select($ranked[.][0] | ready and (blocked | not))] | first) as $at
| ($ranked[:$at // ($ranked | length)]
    | reduce .[] as $entry ([]; if any(.[]; .number == $entry[0].number) then . else . + [$entry[0]] end)
    | .[] | if blocked then "blocked: #\(.number)" else needs end),
  ($at // empty | $ranked[.] | (.[0] | quoted(unstated_axes)[] | "restate: \(.)"), "\(.[0].number)\t\(.[1])\t\(.[0].title)")
