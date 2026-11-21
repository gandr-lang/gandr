# The findings of `check:retired` (#8188), one line each. The input is the
# array of the lines that `git grep -n` prints, `<file>:<line>:<text>`. A line
# gives a finding for an identifier `Retired<Name>` and for the phrases
# `retired spelling`, `retired form`, `old spelling` and `old form`, in any
# case. The plain word `retired` stays free, so a retired job or slot gives
# none.
def marks:
  [ (match("\\bRetired[A-Z][A-Za-z0-9_]*"; "g") | .string),
    (match("\\b(retired|old) (spelling|form)s?\\b"; "gi") | .string) ];

.[]
| select(length > 0)
| capture("^(?<file>[^:]+):(?<line>[0-9]+):(?<text>.*)$")
| . as $hit
| ($hit.text | marks)[]
| "\($hit.file):\($hit.line): `\(.)` marks a form as retired; state what the code does now, or take the item out"
