# The claim order (#2533, `tracker.md` § tracker-claims): the next item a
# seat on an area claims, as one `number<TAB>bucket<TAB>title` line, or none.
#
# Input:
#   area     the area's label, `area:<name>`
#   issues   the open issues: [{number, title, labels: [name], parent}], parent
#            the number of the issue's parent, or null
#   order    each open epic's sub-issues in the epic's order: {"<epic>": [number]}
#
# An issue is a candidate when it is unowned (no `status:claimed`), not ruled
# out (`status:deferred`, `status:discarded`) and not an epic. The buckets, in
# order: a `kind:defect` in the area, then any `kind:defect`; a
# `kind:performance`; a `kind:gap` in the area, cheapest first by its
# `effort:` label (`easy`, `medium`, `hard`, `unknown`, then none); then a
# planned unit, an issue in the area whose parent is an open epic not itself
# deferred, the oldest epic first and its sub-issues in the epic's order.
# Within a bucket the oldest issue comes first.

def has($label): .labels | index($label) != null;
def candidate:
  (has("status:claimed") or has("status:deferred") or has("status:discarded") or has("kind:epic")) | not;
def effort:
  ["effort:easy", "effort:medium", "effort:hard", "effort:unknown"] as $ranks
  | [.labels[] as $l | $ranks | index($l) | values] | min // 4;

.area as $area
| .order as $order
| [.issues[] | select(has("kind:epic") and (has("status:deferred") | not)) | .number] as $epics
| [.issues[] | select(candidate)] as $open
| [
    ($open | map(select(has("kind:defect") and has($area))) | sort_by(.number) | .[] | [., "defect"]),
    ($open | map(select(has("kind:defect"))) | sort_by(.number) | .[] | [., "defect"]),
    ($open | map(select(has("kind:performance"))) | sort_by(.number) | .[] | [., "performance"]),
    ($open | map(select(has("kind:gap") and has($area))) | sort_by(effort, .number) | .[] | [., "gap"]),
    ($open
      | map(select(has($area) and .parent != null) | .parent as $p | select($epics | index($p) != null))
      | sort_by(.parent, (.number as $n | $order["\(.parent)"] // [] | index($n) // infinite), .number)
      | .[] | [., "planned"])
  ]
| first // empty
| "\(.[0].number)\t\(.[1])\t\(.[0].title)"
