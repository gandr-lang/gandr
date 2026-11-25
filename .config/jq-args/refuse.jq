# The refusals of `check:jq-args` (#7091). The input is
# `{added: [{file, line, text}], small: [string]}`: the lines that a change
# adds to a workflow script, and the entries of `small.txt`. An entry is an
# option and a name, such as `--argjson n`.
#
# A line refuses when `--arg` or `--argjson` takes a shell expansion and the
# option with its name is not an entry. The kernel refuses one argument past
# 128 KiB, so a value of unbounded size goes to jq in a file. A comment line
# passes. The output is one refusal for each such argument, in the order of
# the lines.
.small as $small
| [ .added[]
    | . as $added
    | select(.text | test("^\\s*#") | not)
    | .text
    | match("(--arg(?:json)?)\\s+([A-Za-z_][A-Za-z_0-9]*)\\s+\"?\\$"; "g")
    | [.captures[].string]
    | select(join(" ") | IN($small[]) | not)
    | "\($added.file):\($added.line): \(.[0]) \(.[1]) takes a shell value. Give a value of unbounded size to jq in a file with --slurpfile or --rawfile. The name of a small value goes in .config/jq-args/small.txt."
  ]
