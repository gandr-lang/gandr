# The Rust files of a change that change only comments (#5498). A file whose
# diff adds and removes only `//` comment lines and blank lines has no test
# for lldb to stop in, as a change that touches no Rust has none (#3784).
#
# Input: the text of `git diff -U0 --no-renames --no-color <base> HEAD -- '*.rs'`.
# Output: the path of each such file, in the order of the diff.

reduce (split("\n")[]) as $line ({path: null, hunk: false, files: []};
  if ($line | startswith("diff --git ")) then
    .path = ($line | capture("^diff --git a/.* b/(?<path>.*)$").path)
    | .hunk = false
    | .files += [{path: .path, code: false}]
  elif ($line | startswith("@@ ")) then
    .hunk = true
  elif .hunk and ($line | test("^[+-]")) and ($line[1:] | test("^\\s*(//.*)?$") | not) then
    .files[-1].code = true
  else . end)
| [.files[] | select(.code | not) | .path]
