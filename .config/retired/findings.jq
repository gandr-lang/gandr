# This program gives the findings of `check:retired`, one line each. The input
# is the array of the lines that `git grep -n` prints, `<file>:<line>:<text>`.
# A line gives a finding for an identifier `Retired<Name>` and for the phrases
# `retired spelling`, `retired form`, `old spelling` and `old form`, in any
# case. The plain word `retired` stays free, so a retired job or slot gives
# none.
# - see: #8188
#
# `$record` is the text of the record list. Each line holds a path and the
# open issue that removes the record. The paths hold the one record of a
# spelling that the grammar still parses until that issue removes it. There
# the phrase `old spelling` names the record, and it gives no finding. The
# list leaves with the record.
# - see: `.config/retired/record.txt`, `Removal::By`
($record | split("\n") | map(select(length > 0) | split(" ") | .[0])) as $kept
| def marks($file):
  [ (match("\\bRetired[A-Z][A-Za-z0-9_]*"; "g") | .string),
    (match("\\b(retired|old) (spelling|form)s?\\b"; "gi") | .string
     | select(($kept | index([$file])) == null
              or (ascii_downcase | test("^old spellings?$")) == false)) ];

.[]
| select(length > 0)
| capture("^(?<file>[^:]+):(?<line>[0-9]+):(?<text>.*)$")
| . as $hit
| ($hit.text | marks($hit.file))[]
| "\($hit.file):\($hit.line): `\(.)` marks a form as retired; state what the code does now, or take the item out"
