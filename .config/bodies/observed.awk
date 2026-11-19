# The `### Observed` block `evidence:obligations` writes into a pull
# request's body (#3758), spliced in place of the one the body carries.
#
# Input: the body, and the block in the environment as `block`, the lines
# `observed.jq` writes between their markers. The block spans lines, and
# macOS's awk refuses a newline in a `-v` value, so it never comes through
# `-v` (#3784).
#
# Output: the body without its old block, the new one after the
# `## Re-verification` section's end marker, or at the end when the body has
# none. An empty block leaves the body without one.
BEGIN { block = ENVIRON["block"] }
/^<!-- gandr-observed:start -->$/ { skip = 1 }
!skip { print }
/^<!-- gandr-observed:end -->$/ { skip = 0; next }
/^<!-- quenchant-obligations:end -->$/ && !skip && block != "" { print block; placed = 1 }
END { if (!placed && block != "") print block }
