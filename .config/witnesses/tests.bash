#!/usr/bin/env bash
# The tests whose own attributes hold a `#[cfg(…)]`, as a JSON array of
# `{crate, name, site, cfg}` (#4441): the crate is the directory under
# `crates/`, the site `<path>:<line>` of the `fn`, and `cfg` the text inside
# each `#[cfg(…)]`. `check:witnesses` resolves a witness this host builds no
# test for against them (`resolve.jq`).
#
# Usage: tests.bash [root]. Every `*.rs` under `<root>/crates` is read. A test
# is a `fn` whose attributes, read back to the last line that is not an
# attribute, a comment or blank, hold `#[test]`; a `cfg` on its module is not
# read.
set -euo pipefail
cd "${1:-.}"
[[ -d crates ]] || { echo "tests.bash: no crates directory under ${1:-.}" >&2; exit 2; }
mapfile -t sources < <(find crates -name '*.rs' -type f | LC_ALL=C sort)
(( ${#sources[@]} > 0 )) || { echo '[]'; exit 0; }
awk '
  FNR == 1 { attributes = ""; depth = 0 }
  # An attribute, a multi-line one read to its closing bracket.
  depth > 0 || /^[[:space:]]*#\[/ {
    attributes = attributes " " $0
    depth += gsub(/\[/, "[") - gsub(/\]/, "]")
    next
  }
  /^[[:space:]]*(\/\/|$)/ { next }
  match($0, /^[[:space:]]*(pub(\([^)]*\))? )?(async )?fn [A-Za-z0-9_]+/) {
    name = substr($0, RSTART, RLENGTH)
    sub(/.*fn /, "", name)
    if (attributes ~ /#\[test\]/) {
      rest = attributes
      while ((start = index(rest, "#[cfg(")) > 0) {
        rest = substr(rest, start + 6)
        # The predicate runs to the bracket closing `cfg(`.
        open = 1
        for (at = 1; at <= length(rest) && open > 0; at++) {
          c = substr(rest, at, 1)
          if (c == "(") open++
          else if (c == ")") open--
        }
        split(FILENAME, parts, "/")
        printf "%s\t%s\t%s:%d\t%s\n", parts[2], name, FILENAME, FNR, substr(rest, 1, at - 2)
      }
    }
  }
  { attributes = "" }
' "${sources[@]}" \
  | jq -R -s '[split("\n")[] | select(length > 0) | split("\t") | {crate: .[0], name: .[1], site: .[2], cfg: .[3]}]
      | group_by(.site) | map(.[0] + {cfg: map(.cfg | gsub("\\s+"; " ") | ltrimstr(" ") | rtrimstr(" "))})'
