# The claim order (#2533, `tracker.md` § tracker-claims): the next item a
# seat on an area claims, as one `number<TAB>bucket<TAB>title` line, or none,
# after one `collector: #n (k open rows)` line for each collector in the
# area (#3111), one `blocked: #n` line for each issue ranked ahead of it that
# waits on an open issue, one `sections due: #n — <finding>` line for each
# section the pick lacks (#3134), and one `restate: `<axis>`: <question>`
# line for each of the pick's readings still the migration's `unstated`
# placeholder (#2955).
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
# `collector`, whose rows a guard keeps and other issues work (#2621); a
# collector in the area is printed with its open rows instead, so the carving
# due is seen. The buckets, in order: a `kind:defect` in the area; a
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
# without which `pr:open` refuses the landing (`opening.jq`). Each candidate
# ranked ahead of the pick that an open issue blocks is named once, so the
# seat sees why it was passed over. A pick whose reading is the `unstated`
# placeholder is claimed all the same, its axes' questions printed first.

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
def unstated_axes: [.body // "" | marks | select(.reason | unstated) | .axis];
def quoted($marked): [axes[] | . as $axis | select($marked | index($axis)) | "`\($axis)`: \(questions[$axis])"];
def blocked: (.blocked // 0) > 0;

# A collector's open rows (#3111): its unchecked `- [ ]` items, and its table
# rows, header and rule left out, none of whose cells opens `landed` or
# `fixed`. A `## Readings` or `## Concerns` table is a unit's shape, not rows.
def rule: test("^\\s*\\|(\\s*:?-+:?\\s*\\|)+\\s*$");
def open_rows:
  (.body // "" | lines
    | reduce .[] as $line ({shape: false, kept: []};
        (if $line | test("^## ") then .shape = ($line | test("^## (Readings|Concerns)\\s*(:.*)?$")) else . end)
        | if .shape then . else .kept += [$line] end)
    | .kept) as $lines
  | ([$lines[] | select(test("^\\s*[-*] \\[ \\]"))] | length)
    + ([range(0; $lines | length) as $i
        | $lines[$i]
        | select(test("^\\s*\\|") and (rule | not))
        | select(($lines[$i + 1] // "" | rule) | not)
        | select(test("\\|\\s*(landed|fixed)\\b"; "i") | not)]
       | length);

.area as $area
| .order as $order
| [.issues[] | select(has("kind:epic") and (has("status:deferred") | not)) | .number] as $epics
| [.issues[] | select(candidate)] as $open
| [
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
| ([.issues[] | select(has("collector") and has($area))] | sort_by(.number) | .[] | open_rows as $k | "collector: #\(.number) (\($k) open row\(if $k == 1 then "" else "s" end))"),
  ([range(0; $ranked | length) | select($ranked[.][0] | blocked | not)] | first) as $at
| ($ranked[:$at // ($ranked | length)]
    | reduce .[] as $entry ([]; if any(.[]; .number == $entry[0].number) then . else . + [$entry[0]] end)
    | .[] | "blocked: #\(.number)"),
  ($at // empty | $ranked[.]
    | (.[0] | .number as $n | .body // "" | findings | "sections due: #\($n) — \(.)"),
      (.[0] | quoted(unstated_axes)[] | "restate: \(.)"),
      "\(.[0].number)\t\(.[1])\t\(.[0].title)")
