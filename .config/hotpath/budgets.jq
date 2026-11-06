# The budgets of one hotpath policy that its report cannot judge (#5125).
#
# Input: {policy, metric, budgets}: the policy's path, the allocation metric
# of the report it judges (`count` or `bytes`), and its
# `[[functions.budgets]]` tables.
# Output: the `match` of each budget that bounds `alloc` while the report
# counts allocations, in the order of the policy. hotpath takes the `alloc`
# of a function budget only in bytes, so such a budget judges nothing.

if .metric == "bytes" then [] else [.budgets[] | select(.alloc != null) | .match] end
