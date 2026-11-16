# The refusals for the issues that a body works: one line for each issue
# that `pr:open` must not land yet, or nothing.
#
# Input: `{issues: [{number, labels: [name], body}]}`, the issues that the
# body works, as `opening.jq` reads them. The named argument `concerns` gives
# the concerns that `findings` checks against.
#
# The claim's first obligation is the issue's sections. An issue that fails
# `unit:check` is refused with each finding. An issue that passes needs no
# sign-off. The task does not read an epic or a `collector`, which keeps its
# own shape.
# - see: #3134, #7792, `findings.jq`, `units.md` § units-claim

include "findings";

def has($label): .labels | index($label) != null;

.issues[]
| select((has("kind:epic") or has("collector")) | not)
| .number as $n
| .labels as $labels
| [.body // "" | findings($labels)] as $owed
| select($owed | length > 0)
| "#\($n) still lacks what a unit issue carries: write each on the issue, pass `unit:check \($n)`, then run `pr:open` again:\n"
  + ($owed | map("  - \(.)") | join("\n"))
