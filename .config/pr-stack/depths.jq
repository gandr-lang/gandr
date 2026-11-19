# The depth of each open pull request in its stack (#5074): 1 for one on the
# trunk, and one more for each open pull request below it, found by the base
# each one stands on, as `chain.jq` walks it down.
#
# Input: the open pull requests, each with `head` (its branch) and `base`.
# Argument: `$trunk`, the trunk of `trunk.bash`. A pull request on another
# branch that no open pull request heads, as `landing` during its try, is at
# depth 1.
# Output: the same pull requests, each with `depth`. A walk stops at 64.

. as $open
| def below($pr): if $pr.base == $trunk then empty else ([$open[] | select(.head == $pr.base)] | first // empty) end;
  map(. + {depth: ([limit(64; recurse(below(.)))] | length)})
