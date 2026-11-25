# The paths of the rows of the table of artifacts. The table has each
# tracked file that a program writes, with its kind. A kind is an output, a
# ratchet, a first input, a record or a record of one moment. A row with a
# `check` is a generated file that its check writes again and compares.
#
# The script that replays a branch uses these rows, and the stack script uses
# them too. Each of the two ignores a row without a `check`.
#
# - see: `.config/replay/artifacts.json`
# - see: `.config/replay/due.jq`
# - see: `.config/pr-stack/shared.jq`
# - see: #6144
# - see: #7207
#
# A path that ends in `/` holds every path under it; any other path holds
# that file alone.

# Whether a prefix of `$prefixes` holds a path of `$paths`.
def holds($prefixes; $paths):
  any($paths[]; . as $path | any($prefixes[]; . as $prefix | $path == $prefix or (($prefix | endswith("/")) and ($path | startswith($prefix)))));

# A row that has a check.
def checked:
  select(.check != null);

# A row, or one row for each crate of `$crates` when the row has
# `each: "crate"`, `{crate}` read as the crate's directory name.
def expanded($crates):
  if .each == "crate" then
    del(.each) as $row | $crates[] as $crate | $row | walk(if type == "string" then gsub("\\{crate\\}"; $crate) else . end)
  else . end;
