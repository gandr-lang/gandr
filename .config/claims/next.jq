# The claim order (#2533, `tracker.md` § tracker-claims): the next item a
# seat on an area claims, as one `number<TAB>bucket<TAB>title` line, or none,
# after one `collector: #n (k open rows)` line for each collector in the
# area (#3111), one `unsectioned: #n` line for each candidate in the area a
# filer marked `status:unsectioned` (#3112), one `needs sections: #n` or
# `blocked: #n` line for each other issue ranked ahead of it that lacks a
# unit's sections or waits on an open issue, and one `restate: `<axis>`:
# <question>` line for each of the pick's readings still the migration's
# `unstated` placeholder (#2955).
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
# first candidate `unit:check` passes
# (`findings.jq`, #2744) and no open issue blocks (#2902); each one ranked
# ahead of it that fails either is named once, as blocked when it is, so the
# coordinator sees whose sections to write and the seat why it was passed
# over. An issue a filer marked `status:unsectioned` and still lacking its
# sections is named as such, ranked ahead or not, so the coordinator writes
# exactly those sections (#3112). A
# `needs sections:` line quotes the question of each axis whose
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
  ($open | map(select(has($area) and has("status:unsectioned") and (ready | not))) | sort_by(.number) | .[] | "unsectioned: #\(.number)"),
  ([range(0; $ranked | length) | select($ranked[.][0] | ready and (blocked | not))] | first) as $at
| ($ranked[:$at // ($ranked | length)]
    | reduce .[] as $entry ([]; if any(.[]; .number == $entry[0].number) then . else . + [$entry[0]] end)
    | .[] | select(has("status:unsectioned") and (ready | not) | not) | if blocked then "blocked: #\(.number)" else needs end),
  ($at // empty | $ranked[.] | (.[0] | quoted(unstated_axes)[] | "restate: \(.)"), "\(.[0].number)\t\(.[1])\t\(.[0].title)")
