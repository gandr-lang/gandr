# The functions of one crate and the witnesses each one's adequacy section
# names, read from the crate's rustdoc JSON (#1456): the index the
# obligations report reads, so a mutant is tested by the tests the evidence
# chain already ties to its function.
#
# Input: a crate's rustdoc JSON (`evidence:rustdoc`).
# Output: one `{file, begin, end, witnesses}` per function: the file and the
# first and last lines its definition spans, and the path of each
# `- witness: `path`` bullet in its documentation, in order.

[.index[]
  | select(.span != null and (.inner | has("function")))
  | {
      file: .span.filename,
      begin: .span.begin[0],
      end: .span.end[0],
      witnesses: [(.docs // "") | split("\n")[] | capture("^- witness: `(?<path>[^`]+)`") | .path]
    }]
