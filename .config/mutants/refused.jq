# The mutants that one `cargo check` of a schema refuses (#6878): each error
# on an arm's lines takes the names the arm drops out of the schema.
#
# Input: an object with
#   arms      `schema.jq`'s arms;
#   messages  the `compiler-message` records of `cargo check
#             --message-format=json`, as cargo prints them.
#
# Output: `{dropped, unplaced}`: `dropped` the names that the errors take
# out, each once; `unplaced` each error's `file:line` that no arm holds, or
# `?` for an error with no primary span. An unplaced error stops the rounds:
# no mutant that the schema could drop causes it.

. as $in
| [$in.messages[]
    | select(.reason == "compiler-message" and .message.level == "error")
    | (first(.message.spans[] | select(.is_primary)) // null)
    | if . == null then {file: null, line: null} else {file: .file_name, line: .line_start} end] as $errors
| [$errors[] | . as $error | first($in.arms[] | select(.file == $error.file and .first <= $error.line and $error.line <= .last)) // {error: $error}] as $placed
| {dropped: [$placed[] | .drop // empty | .[]] | unique,
   unplaced: [$placed[] | .error // empty | if .file == null then "?" else "\(.file):\(.line)" end] | unique}
