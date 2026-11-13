# A ladder rung's body with the rung before it in its `## After` (#2902), as
# `epic:order --chain` writes it back: `with_after` in `sections.jq`.
#
# Input: {body, after, epic}, after the number of the rung before it and epic
# the ladder's epic.

include "sections";

. as $rung | $rung.body | with_after($rung.after; "the rung before it in #\($rung.epic)'s order")
