# What the issues workflow does to one issue (#3113): `status:unsectioned`
# stands exactly while the body fails `unit:check`'s reading (`unit.jq`),
# and one comment opening `<!-- unit:check -->` lists the findings,
# rewritten in place on each run, never a second one. A pass takes the label
# off and rewrites the comment to say so; an issue never flagged gets no
# comment. An epic or a `collector` keeps its own shape and is not read: the
# label comes off and a standing comment says why. A closed issue is left as
# it is.
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
         "\(marker)\n**unit:check:** not read: an epic or a `collector` keeps its own shape (`units.md` § units-issue).\n"
       elif $failing then
         "\(marker)\n<details><summary>unit:check: \($in.findings | length) finding\(if ($in.findings | length) == 1 then "" else "s" end); labelled <code>status:unsectioned</code> until each is written</summary>\n\n"
         + ($in.findings | map("- \(.)") | join("\n"))
         + "\n\n</details>\n\n`claim:next` passes this issue over while the label stands (`units.md` § units-issue). This comment is rewritten on every edit.\n"
       else
         "\(marker)\n**unit:check:** sections complete; `status:unsectioned` is off.\n"
       end) as $text
    | {label: (if $failing and (has("status:unsectioned") | not) then "add"
               elif ($failing | not) and has("status:unsectioned") then "remove"
               else null end),
       comment: (if $standing != null then (if ($standing.body | settled) == ($text | settled) then null else {act: "edit", id: $standing.id, body: $text} end)
                 elif $failing then {act: "create", body: $text}
                 else null end)}
  end
