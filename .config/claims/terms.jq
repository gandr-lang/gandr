# What a unit's vocabulary owes its `## Sources` (#3158): one finding per
# row of the term map (`.config/references/terms.toml`) whose `match` the
# unit's title and prose meet while its `## Sources` names none of the row's
# `owns`, or nothing.
#
# Input: `{title, body, terms: [{name, match, owns: [key], reason}]}`.
#
# The prose is the title and the body less `## Sources`, `## Readings` and
# `## Concerns`: those sections answer the vocabulary, and the axes' and the
# concerns' names are fixed. An owner is named when its key stands in
# `## Sources`: a page's filename (a `§` after it names a section and is no
# part of the key), a tree path, or `#<issue>` not followed by a digit. A row
# whose role is `not read` names it too, so a seat may decline (#3594).

include "sections";

def key: sub("\\s*§.*$"; "");
def named($text):
  key as $key
  | if startswith("#") then $text | test("\($key)(?![0-9])")
    else $text | contains($key)
    end;

. as $in
| ($in.body // "" | lines
    | reduce .[] as $line ({kept: [], skip: false};
        (if $line | test("^## ") then .skip = ($line | test("^## (Sources|Readings|Concerns)\\s*(:.*)?$")) else . end)
        | if .skip then . else .kept += [$line] end)
    | .kept | join("\n")) as $rest
| (($in.title // "") + "\n" + $rest) as $prose
| ($in.body // "" | section("Sources") // [] | join("\n")) as $sources
| $in.terms[]
| . as $row
| ([$prose | match($row.match; "gi").string] | unique) as $met
| select($met | length > 0)
| select(any($row.owns[]; named($sources)) | not)
| "terms: \($met | map("`\(.)`") | join(", ")) name\(if ($met | length) == 1 then "s" else "" end) \($row.name), owned by \($row.owns | map("`\(.)`") | join(", ")) (\($row.reason)): cite one in `## Sources`, or add the row `| `<owner>` | not read | <why> |`"
