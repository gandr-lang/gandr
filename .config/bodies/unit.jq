# Whether an issue is a unit issue work may start on (#2532): one line per
# missing or malformed section, or nothing. `unit:check` prints them.
#
# Input: the issue's body, as a string; its labels come as the named argument
# `labels`, none when it is not passed, and its number as `number`, none for
# a body no issue holds yet. The reading is `findings.jq`'s.

include "findings";

findings($ARGS.named.labels // []; $ARGS.named.number // null)
