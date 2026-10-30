# What `bench:stress` prints for its bounded check of `library/math` (#3855):
# `rows` when the check passes, `past bound` when it meets the memory bound or
# the wall-clock limit, never retried larger. Under `ulimit -v` the driver's
# failed allocation aborts it, and its errors hold `memory allocation of`. Any
# other failure refuses: the library does not check.
#
# Input: {status: number, out_of_memory: boolean}. Output: the outcome, as
# text.
include "bound";

if .status == 0 then
  "rows"
elif past_bound then
  "past bound"
else
  error("the check exits \(.status)")
end
