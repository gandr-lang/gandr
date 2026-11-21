# A title reaches GitHub as the text a reader sees. A filer that quotes a
# title for the shell with a JSON encoder writes each character outside ASCII
# as an escape `\uXXXX`, and a shell keeps that escape as text. `body:check`
# runs this rule on the title that `issue:file` and `pr:open` write.
#
# Input: the title, a string.
#
# Output: one line for each distinct escape the title holds, in the order of
# its first place, and no line for a title that holds none.

[match("\\\\u[0-9A-Fa-f]{4}"; "g").string]
| reduce .[] as $escape ([]; if index([$escape]) == null then . + [$escape] else . end)
| .[]
| "`\(.)` is a JSON escape, not the character it encodes"
