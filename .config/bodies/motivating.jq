# What a unit owes its epics' motivating sources (#5855): one finding per
# epic the unit names whose `## Motivating sources` has keys, none of which
# the unit's `## Sources` cites, or nothing.
#
# Input: `{body, epics: [{number, body}]}`, the epics those the body names as
# its own (`epic_refs`), read by `unit:check`.
#
# A frame partitions into epics, and each epic into units in one theory area.
# The epic's section keeps the sources that motivate the frame, so a unit cut
# from it still reads them. A key is cited as the term map cites an owner
# (`cited` in `sections.jq`): a row whose role is `not read` cites it too, so
# a seat may decline with its reason. An epic with no section, or a section
# with no backquoted key, asks nothing.

include "sections";

(.body // "" | section("Sources") // [] | join("\n")) as $sources
| (.epics // [])[]
| .number as $epic
| ([.body // "" | source_rows("Motivating sources") | .keys[] | source_key] | unique) as $keys
| select($keys | length > 0)
| select(any($keys[]; cited($sources)) | not)
| "`## Sources` cites none of the motivating sources of #\($epic), the unit's epic: \($keys | map("`\(.)`") | join(", ")). Cite one in `## Sources`, or add the row `| `<source>` | not read | <why> |`"
