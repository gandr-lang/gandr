# The skips of one crate under Miri against its rows in the list. The input
# is `{crate, list, stated, found}`. `stated` holds the reason of each row of
# the crate in `list`. `found` holds the reason of each Miri skip in the crate.
# Each holds its reasons in any order.
#
# The two agree when each reason has as many rows as skips. Then the output is
# the crate and its count of skips. Otherwise the program halts with each
# reason whose counts differ, and the two counts.
def counts: group_by(.) | map({key: .[0], value: length}) | from_entries;
(.stated | counts) as $rows
| (.found | counts) as $skips
| [($rows + $skips) | keys[]
    | {why: ., rows: ($rows[.] // 0), skips: ($skips[.] // 0)}
    | select(.rows != .skips)
    | "  \(.rows) row(s), \(.skips) skip(s): \(.why)"] as $differ
| if $differ == [] then
    "\(.crate): \(.found | length) skip(s), each a row of the list"
  else
    ("the skips of `\(.crate)` under Miri differ from \(.list); each skip in the crate is a row of its list, with the same reason:\n"
      + ($differ | join("\n")) + "\n")
    | halt_error(1)
  end
