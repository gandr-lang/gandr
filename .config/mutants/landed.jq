# The body of a landed pull request's survivors issue (#1456, #3596), which
# `ci:mutants-landed` files. Its first sentence says what the issue is. The
# pull request's last mutants report follows, less its marker line.
#
# Input: `{pr, report}`. `pr` is the pull request's number, and `report` the
# body of its last mutants comment. Output: the issue's body, as raw text.

"This issue lists the mutants of the lines of #\(.pr) that no witness catches.\n\n"
+ "Each survivor needs a witness, or a `- witness:` bullet that its function lacks. The last mutants report of #\(.pr) follows.\n\n"
+ (.report | sub("^<!-- gandr-mutants -->\r?\n"; ""))
