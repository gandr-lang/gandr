# Whether an issue is a unit issue work may start on (#2532): one line per
# missing or malformed section, or nothing. `unit:check` prints them.
#
# Input: the issue's body, as a string. The named argument `labels` gives its
# labels, and an absent argument gives none. The reading is `findings.jq`'s.

include "findings";

findings($ARGS.named.labels // [])
