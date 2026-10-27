# The sections of an issue or pull request body, read the one way
# `opening.jq` and `unit.jq` read them (#2499, #2532).
#
# A section is the lines under a `## <name>` heading, up to the next `## `
# heading; the heading may carry a remark after a colon
# (`## Sources read: none requested`). An item is a line `- <head> — <text>`:
# its keys are the head's backquoted spans, so `` - `units.md` § units-pr —
# … `` keys `units.md`, and one line may key several sources. A row is a
# table line, read as its cells.

# The body's lines, a carriage return dropped from each.
def lines: split("\n") | map(sub("\r$"; ""));

# The lines of the section headed `## $name`, or null when the body has none.
def section($name):
  lines as $lines
  | ([range(0; $lines | length) | select($lines[.] | test("^## \($name)\\s*(:.*)?$"))] | first) as $start
  | if $start == null then null
    else $lines[$start + 1:] as $rest
    | ([range(0; $rest | length) | select($rest[.] | test("^## "))] | first // ($rest | length)) as $end
    | $rest[:$end]
    end;

# A section's list items: its lines opening `- ` or `* `.
def items: .[] | select(test("^[-*] "));

# An item as {line, keys, text}, or null when it is not `- <head> — <text>`
# with at least one backquoted key in its head.
def keyed:
  . as $line
  | (capture("^[-*] (?<head>.+?) —\\s*(?<text>.*)$") // null)
  | if . == null then null
    else [.head | match("`([^`]+)`"; "g") | .captures[0].string] as $keys
    | if ($keys | length) == 0 then null else {line: $line, keys: $keys, text: (.text | sub("\\s+$"; ""))} end
    end;

# A `## Sources read` item replacing a source,
# `- supersedes: `<old key>` — <confirmation>`, as {line, old, confirmation},
# or null.
def supersession:
  . as $line
  | (capture("^[-*] supersedes: `(?<old>[^`]+)` —\\s*(?<confirmation>.*)$") // null)
  | if . == null then null else {line: $line, old, confirmation: (.confirmation | sub("\\s+$"; ""))} end;

# The old keys the body's `## Sources read` supersedes.
def superseded: [(section("Sources read") // []) | items | supersession | select(. != null) | .old] | unique;

# A section's lines before its first `### ` subsection.
def lead: ([range(0; length) as $i | select(.[$i] | test("^### ")) | $i] | first) as $end | if $end == null then . else .[:$end] end;

# A section's table rows but the header's rule, each as {line, cells}: the
# cells trimmed, a cell wrapped whole in backquotes unwrapped.
def rows:
  .[]
  | select(test("^\\s*\\|"))
  | . as $line
  | sub("^\\s*\\|"; "") | sub("\\|\\s*$"; "") | split("|")
  | map(gsub("^\\s+|\\s+$"; "") | if test("^`[^`]*`$") then .[1:-1] else . end)
  | select(all(test("^:?-+:?$")) | not)
  | {line: $line, cells: .};

# The seven reading axes (`units.md` § units-readings).
def axes: ["univalent", "oracle", "descent", "located", "resident", "rewriting", "zero-cost"];

# The question each axis asks of a unit (`units.md` § units-readings), quoted
# where a reading is refused so the writer has it in front of them (#2955).
def questions:
  {univalent: "what univalence and the rewriting core give the construction: an equation, a transported rule, a replayed cell, representation independence",
   oracle: "which part is decided by certificate replay and which is computed; which modality or dominance classifies it",
   descent: "the local data, the interface, the assembly; what a change invalidates and reuses; the parallel width left",
   located: "at which world a judgement or value is meaningful; what crosses worlds or sessions, and by what: by location inside one world (a LAM: region, index, never recycled) or by content across worlds (the CAM: `cam_commit` at the source, `cam_deref` at the destination); whether what crosses is `mobile` (authority) and `Open` (no location pointer)",
   resident: "representation, sharing, persistence; which memory holds the value — a location-addressable store (the runtime's heaps, `core-sequent`'s store) or the content-addressable store (`storage-values`, chunk and content pointer) — and what the crossing between them costs (the boundary and alias classification, the locality bound); where integrity stops and replay decides",
   rewriting: "rules and normal forms; rewrites between rewrites; which coherence tier settles them",
   "zero-cost": "what the change adds at run time and what demands it: a grade above zero, a crossing a located mode names or a branch a session type carries (then it is the program, not overhead), or a recipe policy off by default (then the artifact built without it carries none of its bytes and the checker refuses the forms that need it); what the grade erases; what a hand-written form would cost against it"};

# The marks of an issue's `## Readings` table, read before its subsections:
# per row naming an axis, {axis, mark, reason}, the mark `yes` or `no` from
# the first cell opening with it, or null, and the reason the clause after
# its dash (`no — <why>`), or null when the cell gives none (#2955).
def marks:
  (section("Readings") // [] | lead)
  | rows
  | .cells as $cells
  | first($cells[] | select(IN(axes[]))) as $axis
  | (first($cells[] | capture("^(?<mark>[Yy][Ee][Ss]|[Nn][Oo])\\b\\s*(?:—\\s*(?<reason>.*\\S))?")) // {mark: null, reason: null}) as $read
  | {axis: $axis, mark: ($read.mark | if . == null then null else ascii_downcase end), reason: $read.reason};

# Whether a reading's reason is the migration's placeholder (#2955): the row
# was a bare mark before reasons were required, and is restated at claim.
def unstated: . != null and test("^unstated\\b");

# The axes an issue's `## Readings` selects: a row marked `yes`, or an item
# naming the axis.
def selected:
  [(marks | select(.mark == "yes") | .axis),
   ((section("Readings") // [] | lead) | items | first(match("`([^`]+)`"; "g").captures[0].string | select(IN(axes[]))))]
  | unique;

# The concern ids of `ledger/concerns.sql` (#2795): the tasks that read the
# ledger pass them as `--argjson concerns`; without the argument, the ids as
# of that landing, which the `check:claims` cases are written against.
def concerns: $ARGS.named.concerns // ["fork", "oracle", "sharing"];

# The marks of an issue's `## Concerns` table: per row naming a concern,
# {concern, mark}, the mark `yes` or `no` from a cell reading it alone or
# before its how (`yes — <how>`), or null.
def concern_marks:
  (section("Concerns") // [] | lead)
  | rows
  | .cells as $cells
  | first($cells[] | select(IN(concerns[]))) as $concern
  | {concern: $concern, mark: (first($cells[] | ascii_downcase | capture("^(?<mark>yes|no)\\b").mark) // null)};

# Whether a section has content once its HTML comments are dropped.
def filled: join("\n") | gsub("(?s)<!--.*?-->"; "") | test("\\S");

# The issue's `## After` (#2902): what it waits on, as {empty, none, numbers,
# malformed}, or null when the body has none. A content line, HTML comments
# and blank lines dropped, is `none` or `- #n — <what it waits for>`;
# `numbers` are the items' issues in order, `malformed` the other lines.
def after_none: test("^\\s*none\\.?\\s*$"; "i");
def after_item: test("^[-*] #[0-9]+ —\\s*\\S");
def after:
  (section("After") // null)
  | if . == null then null
    else (join("\n") | gsub("(?s)<!--.*?-->"; "") | split("\n") | map(select(test("\\S")))) as $lines
    | {empty: ($lines | length == 0),
       none: any($lines[]; after_none),
       numbers: [$lines[] | select(after_item) | capture("^[-*] #(?<n>[0-9]+)").n | tonumber],
       malformed: [$lines[] | select((after_none or after_item) | not)]}
    end;

# The body with `#$n` listed in its `## After`, `- #$n — $clause`: the item
# replaces a `none` line, follows the section's last item, or opens the
# section, appended to the body, when it has none. A body already listing it
# is unchanged.
def with_after($n; $clause):
  . as $body
  | "- #\($n) — \($clause)" as $item
  | lines as $lines
  | ([range(0; $lines | length) | select($lines[.] | test("^## After\\s*$"))] | first) as $start
  | if $start == null then ($body | sub("\\s*$"; "")) + "\n\n## After\n\n\($item)\n"
    elif (after.numbers | index($n)) != null then $body
    else ([range($start + 1; $lines | length) | select($lines[.] | test("^## "))] | first // ($lines | length)) as $end
    | ([range($start + 1; $end) | select($lines[.] | test("\\S"))] | last) as $last
    | if $last == null then $lines[:$start + 1] + ["", $item] + (if $end < ($lines | length) then [""] else [] end) + $lines[$end:]
      elif $lines[$last] | test("^\\s*none\\.?\\s*$"; "i") then $lines[:$last] + [$item] + $lines[$last + 1:]
      else $lines[:$last + 1] + [$item] + $lines[$last + 1:]
      end
    | join("\n")
    end;

# The kinds a `## Refactoring` row names (#2884, `units.md` § units-pr).
def refactor_kinds: ["duplicate", "consolidate", "generalise", "split", "delete", "cross-cutting"];

# A refactoring table's rows (#2884), from a section's lines: each row but the
# header (`Kind`) as {line, kind, whereas, observation}, `whereas` the
# backquoted spans of the second cell, or its comma-separated parts when it has
# none. A PR's `## Refactoring` and a filed issue's `## Observation` read alike.
def refactor_rows:
  [rows
    | select((.cells[0] // "" | ascii_downcase) != "kind")
    | {line, kind: (.cells[0] // ""),
       whereas: (.cells[1] // ""
         | if test("`") then [match("`([^`]+)`"; "g") | .captures[0].string]
           else [split(",")[] | gsub("^\\s+|\\s+$"; "") | select(. != "")] end),
       observation: (.cells[2] // "")}];

# The body's `## Refactoring` (#2884), or null when it has none: {verdict,
# rows}. The verdict is the first content line's `yes`, `maybe` or `no`,
# alone or before a dash and a clause, else null; HTML comments are not
# content. The rows are its table's, as `refactor_rows` reads them.
def refactoring:
  (section("Refactoring") // null)
  | if . == null then null
    else (join("\n") | gsub("(?s)<!--.*?-->"; "") | split("\n")) as $lines
    | {verdict: (first($lines[] | select(test("\\S"))) // ""
          | (capture("^\\s*(?<v>yes|maybe|no)(?:\\s+—\\s*\\S.*)?\\s*$") // {v: null}).v),
       rows: ($lines | refactor_rows)}
    end;

# The pull requests a filed refactor issue came from: its `from: #<n>` lines.
def from_lines: [lines[] | capture("^from: #(?<n>[0-9]+)\\s*$") | .n | tonumber];

# Whether a `Where` is spelled as an item path, `crate::path` or a crate
# alone, as rustdoc names it.
def item_path: test("^[A-Za-z_][A-Za-z0-9_]*(::[A-Za-z_][A-Za-z0-9_]*)*$");

# Whether a `Where` is spelled as a repository path: a relative path with a
# `/` or a `.`, and no `::`.
def tree_path: test("^[.A-Za-z0-9_-][^\\s:]*$") and test("[/.]");
