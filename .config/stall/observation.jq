# The observation that opens a stall report (#3112, #3596). Its first
# sentence says what the report is. `## Observation` then gives the finding's
# line in a text block under a one-sentence lead. `stall:watch` files it
# before the sections of the `stall` template.
#
# Input: one finding, `{kind, number, line}`. Output: the observation, as
# raw text.

"This report routes the `\(.kind)` stall of #\(.number) to a seat.\n\n"
+ "## Observation\n\n"
+ "`stall:watch` reads this finding on #\(.number).\n\n"
+ "```text\n\(.line)\n```\n"
