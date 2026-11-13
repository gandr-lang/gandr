# The rows of `## Observed at` (#6873): where a consumer sees the view that
# a unit builds. `unit:check` reads them on an issue labelled `view`
# (`findings.jq`). `pr:open` reads them on a body that closes such an issue
# (`views.bash`, `opening.jq`).
#
# The section is the table `| Surface | How to reach it | Test |`. A row names
# a shipped surface, the way to reach the view there, and the test that
# drives the view. `surfaces.json` lists each shipped surface with the paths
# that hold it, and a surface that it does not list is no shipped surface.
# The first row is the editor extension. Where the view has no form in the
# editor, that row reads `n/a — <why>` in its second cell. On the issue, the
# test cell can read `owed`.

import "surfaces" as $surfaces;
include "sections";

# The shipped surfaces: [{surface, paths}].
def shipped: $surfaces::surfaces[0];

# The shipped surface that a row's first cell names, or null. The names
# compare in lower case.
def surface_named($name): ($name | ascii_downcase) as $key | first(shipped[] | select(.surface == $key)) // null;

# Whether a second cell sets its row aside, as `n/a — <why>` does.
def set_aside: test("^n/a\\b"; "i");

# The rows of the body's `## Observed at` without the header: [{line, cells}].
def observed_rows: [section("Observed at") // [] | rows | select((.cells[0] // "" | ascii_downcase) != "surface")];

# The rows that name a shipped surface and set no surface aside, each as
# {surface, test}: the rows that `pr:open` resolves at HEAD.
def observed_tests:
  observed_rows[]
  | select(surface_named(.cells[0]) != null and ((.cells[1] // "") | set_aside | not))
  | {surface: (.cells[0] | ascii_downcase), test: (.cells[2] // "")};

# The findings of the `## Observed at` of an issue labelled `view`, one line
# each, or nothing. An issue that the coordinator signed is not judged again,
# as for `## Surface`.
def observed_findings($labels):
  if ($labels | index("view")) == null or ($labels | index("shape:signed")) != null then empty
  else
    "the table `| Surface | How to reach it | Test |`, one row for each shipped surface where a consumer sees the view, the editor extension first (`units.md` § units-issue)" as $form
    | ([shipped[].surface] | map("`\(.)`") | join(", ")) as $names
    | observed_rows as $rows
    | if section("Observed at") == null then "`## Observed at` is missing: a `view` unit writes \($form)"
      elif ($rows | length) == 0 then "`## Observed at` holds no row: write \($form)"
      else
        (if ($rows[0].cells[0] | ascii_downcase) == "editor extension" then empty
         else "`## Observed at` opens with `\($rows[0].cells[0])`: the first row is the editor extension, with `n/a — <why>` in its second cell where the view has no form in the editor" end),
        (if any($rows[]; (.cells[1] // "") | set_aside | not) then empty
         else "`## Observed at` names no surface where a consumer sees the view: add a row for a shipped surface (\($names))" end),
        ($rows | to_entries[] | .key as $at | .value
          | (.cells[1] // "") as $reach
          | if surface_named(.cells[0]) == null then
              "`## Observed at` row `\(.line)` names no shipped surface of `.config/claims/surfaces.json` (\($names)): name one, or add the surface to the table in the landing that ships it"
            elif $reach | set_aside then
              if $at > 0 then "`## Observed at` row `\(.line)` sets its surface aside: only the editor extension's row reads `n/a — <why>`, so remove the row"
              elif $reach | test("^n/a —\\s*\\S"; "i") then empty
              else "`## Observed at` row `\(.line)` reads a bare `n/a`: write `n/a — <why the view has no form in the editor>`"
              end
            elif $reach | test("\\S") | not then "`## Observed at` row `\(.line)` gives no way to reach the view: write the command, the gesture or the request"
            elif (.cells[2] // "") | test("\\S") | not then "`## Observed at` row `\(.line)` names no test: write the test that drives the view there, or `owed` on the issue"
            else empty
            end)
      end
  end;
