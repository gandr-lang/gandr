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

# The six reading axes (`units.md` § units-readings).
def axes: ["univalent", "oracle", "descent", "located", "resident", "rewriting"];

# The marks of an issue's `## Readings` table, read before its subsections:
# per row naming an axis, {axis, mark}, the mark `yes` or `no` from a cell
# reading it alone or before its reason (`yes — <why>`), or null.
def marks:
  (section("Readings") // [] | lead)
  | rows
  | .cells as $cells
  | first($cells[] | select(IN(axes[]))) as $axis
  | {axis: $axis, mark: (first($cells[] | ascii_downcase | capture("^(?<mark>yes|no)\\b").mark) // null)};

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
