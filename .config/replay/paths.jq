# The paths of the rows of `artifacts.json` (#6144): the generated files of
# the tree. `due.jq` reads them for a replay, and `shared.jq` of
# `.config/pr-stack` reads them for the stacking (#7207).
#
# A path that ends in `/` holds every path under it; any other path holds
# that file alone.

# Whether a prefix of `$prefixes` holds a path of `$paths`.
def holds($prefixes; $paths):
  any($paths[]; . as $path | any($prefixes[]; . as $prefix | $path == $prefix or (($prefix | endswith("/")) and ($path | startswith($prefix)))));

# A row, or one row for each crate of `$crates` when the row has
# `each: "crate"`, `{crate}` read as the crate's directory name.
def expanded($crates):
  if .each == "crate" then
    del(.each) as $row | $crates[] as $crate | $row | walk(if type == "string" then gsub("\\{crate\\}"; $crate) else . end)
  else . end;
