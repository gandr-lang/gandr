# Whether a comment that sets a unit aside on a probe states the measured
# saving (#6569, `tracker.md` § tracker-issues): one refusal line, or
# nothing.
#
# Input: `{issue, comment}`: the unit's body, and the comment's text.
#
# Each `## Sources` row of the unit whose `saves:` names a saving (it is not
# `n/a — <reason>`) asks the comment for one line `measured: <value> by
# <instrument>`, with a digit in its value. A probe that sets the unit aside
# measures the saving that the design claims, by its instrument, not another
# quantity.

include "sections";

[(.issue // "") | source_rows
  | {keys, saves: (.text | claim_parts | .saves)}
  | select(.saves != null and .saves != "" and (.saves | test("^n/a\\b") | not))] as $claimed
| [(.comment // "") | lines[] | select(test("^\\s*([-*]\\s+)?measured:\\s*[^\\s].*[0-9].*\\bby\\s+\\S"))] as $measured
| select(($claimed | length) > ($measured | length))
| "the comment sets the unit aside on a probe and states \($measured | length) measured saving(s) of the \($claimed | length) that its `## Sources` claims: add one line `measured: <value> by <instrument>` for each, the value read by the instrument that the claim names:\n"
  + ($claimed | map("  - `\(.keys | join("`, `"))` — saves: \(.saves)") | join("\n"))
