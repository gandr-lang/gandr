# Whether the issues a body works are sectioned and signed (#3134): one
# refusal line per issue `pr:open` must not land yet, or nothing.
#
# Input: `{issues: [{number, labels: [name], body}]}`, the issues the body
# works, as `opening.jq` reads them. The concerns `findings` checks against
# come as the named argument `concerns`.
#
# Sectioning is the claim's first obligation (`units.md` § units-claim): an
# issue still failing `unit:check` (`findings.jq`) is refused with each
# finding. A sectioned issue then needs `shape:signed`, the coordinator's
# sign-off on its shape: the seat that sectioned it pages `sections #n:
# <the shape's first line>` and works on meanwhile, but the landing waits for
# the label. An issue sectioned before its claim is signed by construction,
# `issue:file` labelling it as it files a passing body. An epic or a
# `collector` keeps its own shape and is not read.

include "findings";

def has($label): .labels | index($label) != null;

.issues[]
| select((has("kind:epic") or has("collector")) | not)
| .number as $n
| [.body // "" | findings] as $owed
| if ($owed | length) > 0 then
    "#\($n) still lacks what a unit issue carries: write each on the issue, pass `unit:check \($n)`, page the coordinator `sections #\($n): <the shape's first line>` for `shape:signed`, then run `pr:open` again:\n"
    + ($owed | map("  - \(.)") | join("\n"))
  elif has("shape:signed") | not then
    "#\($n)'s sections wait for the coordinator's `shape:signed`: page `sections #\($n): <the shape's first line>` if not yet paged, then run `pr:open` again once the label stands"
  else empty
  end
