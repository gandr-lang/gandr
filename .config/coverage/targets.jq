# The integration targets that the coverage run cannot measure (#7195). A
# target whose file holds no item builds a binary with no coverage map, and
# `cargo llvm-cov report` stops on that object, so `ci:coverage` stops before
# its export, in each part of the night's run.
#
# Input: an array of the integration targets of the tree, each
# {file, name, path, code}: the manifest, the target's name, its path in the
# crate, and the text of that path.
# Output: an array of refusals, one for each target whose text holds no line
# past comments and blank lines.

[.[]
  | select(.code | split("\n") | all(test("^\\s*(//.*)?$")))
  | "\(.file): the integration target `\(.name)` at \(.path) holds no item, so its binary has no coverage data and `cargo llvm-cov report` stops on it (#7195); remove the target until its first case"]
