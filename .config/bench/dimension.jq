# The cylinder and cone built-ins an example names past n = 3, in the order
# written (#3930): `cylcomp(n,k,m)` and `conecomp(n,k,m)` with an argument of 4
# or more, and `cylstack(n)` with n of 4 or more. Catt's lexer reads them with
# no spaces inside. Catt runs only at n = 2 and 3 (#3855), so `bench:catt`
# refuses an example that names one, before Catt runs.
#
# Input: the example's text, as one JSON string. Output: the built-ins, as an
# array of their spellings; empty when the example names none past n = 3.
[
  match("(?:cylcomp|conecomp)\\(\\d+,\\d+,\\d+\\)|cylstack\\(\\d+\\)"; "g").string
  | select([scan("\\d+") | tonumber] | any(. >= 4))
]
