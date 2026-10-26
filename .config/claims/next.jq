# The claim order (#2533, `tracker.md` § tracker-claims): the next item a
# seat on an area claims, as one `number<TAB>bucket<TAB>title` line, or none,
# after one `needs sections: #n` line for each issue ranked ahead of it that
# lacks a unit's sections.
#
# Input:
#   area     the area's label, `area:<name>`
#   issues   the open issues: [{number, title, labels: [name], parent, body}],
#            parent the number of the issue's parent, or null; body the
#            issue's body, or null
#   order    each open epic's sub-issues in the epic's order: {"<epic>": [number]}
#
# An issue is a candidate when it is unowned (no `status:claimed`), not ruled
# out (`status:deferred`, `status:discarded`), not an epic and not a
# `collector`, whose rows a guard keeps and other issues work (#2621). The
# buckets, in order: a `kind:defect` in the area, then any `kind:defect`; a
# `kind:performance` in the area, then any `kind:performance`; a `kind:gap` in
# the area, cheapest first by its `effort:` label (`easy`, `medium`, `hard`,
# `unknown`, then none); then a planned unit, an issue in the area whose
# parent is an open epic not itself deferred, the oldest epic first and its
# sub-issues in the epic's order. Within a bucket the oldest issue comes
# first. The pick is the first candidate `unit:check` passes (`findings.jq`,
# #2744); each one ranked ahead of it that does not is named once, so the
# coordinator sees whose sections to write.

include "findings";

def has($label): .labels | index($label) != null;
def candidate:
  (has("status:claimed") or has("status:deferred") or has("status:discarded") or has("kind:epic")
    or has("collector")) | not;
def effort:
  ["effort:easy", "effort:medium", "effort:hard", "effort:unknown"] as $ranks
  | [.labels[] as $l | $ranks | index($l) | values] | min // 4;
def ready: [.body // "" | findings] | length == 0;

.area as $area
| .order as $order
| [.issues[] | select(has("kind:epic") and (has("status:deferred") | not)) | .number] as $epics
| [.issues[] | select(candidate)] as $open
| [
    ($open | map(select(has("kind:defect") and has($area))) | sort_by(.number) | .[] | [., "defect"]),
    ($open | map(select(has("kind:defect"))) | sort_by(.number) | .[] | [., "defect"]),
    ($open | map(select(has("kind:performance") and has($area))) | sort_by(.number) | .[] | [., "performance"]),
    ($open | map(select(has("kind:performance"))) | sort_by(.number) | .[] | [., "performance"]),
    ($open | map(select(has("kind:gap") and has($area))) | sort_by(effort, .number) | .[] | [., "gap"]),
    ($open
      | map(select(has($area) and .parent != null) | .parent as $p | select($epics | index($p) != null))
      | sort_by(.parent, (.number as $n | $order["\(.parent)"] // [] | index($n) // infinite), .number)
      | .[] | [., "planned"])
  ] as $ranked
| ([range(0; $ranked | length) | select($ranked[.][0] | ready)] | first) as $at
| ($ranked[:$at // ($ranked | length)]
    | reduce .[] as $entry ([]; if index($entry[0].number) == null then . + [$entry[0].number] else . end)
    | .[] | "needs sections: #\(.)"),
  ($at // empty | $ranked[.] | "\(.[0].number)\t\(.[1])\t\(.[0].title)")
