# Whether a unit states the claim of each design page it builds on (#6569,
# `units.md` § units-issue): one line for each `## Sources` row that lacks a
# part of the claim, or nothing.
#
# Input: `{body, absorption, before}`: the issue's body; the vault's page
# statuses as `report:absorption` writes them, `{"<filename>": [{path,
# status}]}`, or null where no vault checkout has written them, as in CI;
# and the body as it stood when this rule landed, for an issue signed by
# then, or null.
#
# A row whose role is primary and that names a vault page whose status is
# `design` or `partly` (the tree does not yet state all of it) carries the
# design's claim in its third cell: `builds: <what the unit keys or builds>`,
# `saves: <what the design saves>, read by <instrument>` and `decides: <what
# the trusted side still decides>`. A page is named by its filename (every
# page that filename names) or by its vault path (that page alone), as
# `absorbing.jq` names it.
#
# The rule stops no unit in flight: while the `## Sources` of an issue
# signed before the rule landed is as it was then, each line is a `note:`,
# and no refusal.

include "sections";

def open_status: IN("design", "partly");

. as $in
| ($in.before != null and (($in.before | section("Sources")) == ($in.body // "" | section("Sources")))) as $kept
| select($in.absorption != null)
| ($in.body // "") | source_rows
| select(.role == "primary")
| . as $row
| [.keys[] | source_key | select(test("^[^\\s]+\\.md$"))
    | . as $name
    | (if test("/") then [$in.absorption[split("/") | last] // [] | .[] | select(.path == $name)]
       else $in.absorption[$name] // [] end) as $entries
    | select(any($entries[]; .status | open_status))
    | $name] as $pages
| select($pages | length > 0)
| ($row.text | claim_parts | claim_gaps) as $gaps
| select($gaps | length > 0)
| "the `## Sources` row of `\($pages | join("`, `"))`, a primary design page, does not state the design's claim (\($gaps | join(", "))): write `builds: <what the unit keys or builds>`, `saves: <what the design saves>, read by <instrument>` and `decides: <what the trusted side still decides>` in its third cell, a part `n/a — <reason>` where the design claims nothing of it (`units.md` § units-issue)"
| if $kept then "note: \(.); the issue was signed before this check landed, so it is not refused until its `## Sources` changes" else . end
