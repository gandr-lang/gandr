# The row `bench:catt` prints for one finished run of Catt (#3930): the
# example and its wall time to the hundredth of a second, or `past bound` where
# the run met a bound (`bound.jq`), never retried larger (#3855). Under
# `ulimit -v` Catt's runtime raises `Out_of_memory`. Any other failure
# refuses: the example does not check.
#
# Input: {example: string, status: number, seconds: number, out_of_memory:
# boolean}. Output: the row, as text.
include "bound";

def hundredths:
  (. * 100 | round) as $cents
  | "\($cents / 100 | floor).\($cents % 100 | tostring | if length < 2 then "0" + . else . end)";

if .status == 0 then
  "| `\(.example)` | \(.seconds | hundredths) s |"
elif past_bound then
  "| `\(.example)` | past bound |"
else
  error("Catt exits \(.status) on \(.example): the example does not check")
end
