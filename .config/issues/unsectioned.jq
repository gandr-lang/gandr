# What the issues workflow does to one issue (#3113): `status:unsectioned`
# stands exactly while the body fails `unit:check`'s reading (`unit.jq`),
# and one comment opening `<!-- unit:check -->` lists its findings in a table. The workflow rewrites this comment in place.
# It never writes a second comment. A pass removes the label. It rewrites the
# comment. An issue that was never flagged gets no comment. An epic or a
# `collector` keeps its own shape. The workflow does not read it. It removes the label.
# It writes a standing comment that gives the reason. A closed issue stays unchanged.
#
# Input: `{state, labels, findings, comments}`: the issue's state (`open` or
# `closed`), its labels, `unit.jq`'s findings as lines, and its comments
# opening with the marker, `[{id, body}]`, oldest first.
# Output: `{label, comment}`: `label` `add`, `remove` or null; `comment`
# null, or `{act, id, body}`, `act` `create` (no `id`) or `edit`.

def marker: "<!-- unit:check -->";
def has($label): .labels | index($label) != null;
# GitHub keeps a comment without its trailing newline, and may store `\r\n`.
def settled: gsub("\r"; "") | sub("\\s+$"; "");

. as $in
| ($in.comments | first // null) as $standing
| if $in.state != "open" then {label: null, comment: null}
  else
    (has("kind:epic") or has("collector")) as $exempt
    | (($in.findings | length) > 0 and ($exempt | not)) as $failing
    | (if $exempt then
         "\(marker)\n**unit:check:** This issue is not read. An epic or a `collector` keeps its own shape (`units.md` § units-issue).\n"
       elif $failing then
         "\(marker)\n**unit:check:** This issue has \($in.findings | length) missing unit section\(if ($in.findings | length) == 1 then "" else "s" end).\n\n"
         + "| Section |\n| --- |\n"
         + ($in.findings | map("| \(.) |") | join("\n"))
         + "\n\nThe seat that claims this issue writes these sections. It then pages for `shape:signed` (`units.md` § units-claim). This comment is rewritten after every edit.\n"
       else
         "\(marker)\n**unit:check:** The unit sections are complete.\n"
       end) as $text
    | {label: (if $failing and (has("status:unsectioned") | not) then "add"
               elif ($failing | not) and has("status:unsectioned") then "remove"
               else null end),
       comment: (if $standing != null then (if ($standing.body | settled) == ($text | settled) then null else {act: "edit", id: $standing.id, body: $text} end)
                 elif $failing then {act: "create", body: $text}
                 else null end)}
  end
