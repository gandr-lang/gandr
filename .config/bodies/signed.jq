# Whether the issues of a body have their sections and their sign-off. The
# result holds one refusal line for each issue that `pr:open` must not land
# yet. It holds a wait for each issue that `pr:open` lands after the
# sign-off. Otherwise it is empty.
# - see: #3134
#
# Input: `{issues: [{number, labels: [name], body}]}`, the issues the body
# works, as `opening.jq` reads them. The concerns `findings` checks against
# come as the named argument `concerns`.
#
# The sections are the claim's first obligation. An issue that fails
# `unit:check` is refused with each finding. An issue with its sections then
# needs `shape:signed`, the coordinator's sign-off on its shape. Its seat
# pages `sections #n: <the shape's first line>` and continues the work, and
# the landing waits for the label.
# - see: `units.md` § units-claim, `findings.jq`
#
# The label is a future event, never a refusal. Its `wait:` line says so.
# Its `arm:` line starts `pr:await` on the issue. The exit of `pr:await`
# wakes the seat, and the seat runs `pr:open` again.
# - see: #4164, `.config/pr-stack/await.jq`
#
# `issue:file` labels a filed issue when it passes `unit:check`. Thus an
# issue with its sections before its claim has its sign-off already. The
# task skips an epic and a `collector`, which keep their own shape.
# - see: #7545

include "findings";
include "await" {search: "../pr-stack"};

def has($label): .labels | index($label) != null;

.issues[]
| select((has("kind:epic") or has("collector")) | not)
| .number as $n
| .labels as $labels
| [.body // "" | findings($labels; $n) | select(startswith("note: ") | not)] as $owed
| if ($owed | length) > 0 then
    "#\($n) still lacks what a unit issue carries: write each on the issue, pass `unit:check \($n)`, page the coordinator `sections #\($n): <the shape's first line>` for `shape:signed`, then run `pr:open` again:\n"
    + ($owed | map("  - \(.)") | join("\n"))
  elif has("shape:signed") | not then
    "wait: #\($n)'s sections wait for the coordinator's `shape:signed`: page `sections #\($n): <the shape's first line>` if not yet paged; `pr:await \($n)` wakes the seat once the label stands, and `pr:open` runs again then\n"
    + arm($n)
  else empty
  end
