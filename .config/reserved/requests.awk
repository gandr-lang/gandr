# The tests that ask for `Width::Reserved` in their own bodies (#7539), read by
# `check.bash`: one line `<file>\t<test function>` for each. A test is a `fn`
# under a `#[test]` attribute. Its body runs from the first `{` after the name
# to the brace that closes it. A comment line asks for nothing.
FNR == 1 {
  pending = 0
  inside = 0
}
/^[[:space:]]*\/\// {
  next
}
/^[[:space:]]*#\[test\]/ {
  pending = 1
  next
}
pending && /^[[:space:]]*(pub(\([a-z]+\))?[[:space:]]+)?fn[[:space:]]+[A-Za-z0-9_]+/ {
  name = $0
  sub(/^[[:space:]]*(pub(\([a-z]+\))?[[:space:]]+)?fn[[:space:]]+/, "", name)
  sub(/[^A-Za-z0-9_].*$/, "", name)
  pending = 0
  inside = 1
  depth = 0
  opened = 0
  asked = 0
}
inside {
  line = $0
  if (line ~ /Width::Reserved/) {
    asked = 1
  }
  opens = gsub(/\{/, "{", line)
  closes = gsub(/\}/, "}", line)
  depth += opens - closes
  if (opens > 0) {
    opened = 1
  }
  if (opened && depth <= 0) {
    if (asked) {
      printf "%s\t%s\n", FILENAME, name
    }
    inside = 0
  }
}
