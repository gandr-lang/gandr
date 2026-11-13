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

# A row's key: its first backquoted span, or its text trimmed when it has
# none, so `` `hold_expression` `` and `hold_expression — …` key alike.
def row_key:
  (capture("`(?<key>[^`]+)`") // null | .key) // (sub("\\s+—.*$"; "") | gsub("^\\s+|\\s+$"; ""));

# A collector body's open rows (#3111, #3326), each by its key: its unchecked
# `- [ ]` items, keyed by the item's text, and its table rows, keyed by the
# first cell, header and rule left out, none of whose cells opens `landed`,
# `fixed`, `accepted` or `runner shift`, the last three the statuses a hotpath
# index settles a row with (#3369). A cell ends at an unescaped `|`, and a
# `\|` in the first cell reads as `|` (#3371), so a mutant name holding one
# keys whole. A `## Sources`, `## Readings`, `## Concerns` or `## Engineering`
# table is a unit's shape, and a `## Settled` table measures settled rows:
# none is rows.
def collector_rows:
  def rule: test("^\\s*\\|(\\s*:?-+:?\\s*\\|)+\\s*$");
  (lines
    | reduce .[] as $line ({shape: false, kept: []};
        (if $line | test("^## ") then .shape = ($line | test("^## (Sources|Readings|Concerns|Engineering|Settled)\\s*(:.*)?$")) else . end)
        | if .shape then . else .kept += [$line] end)
    | .kept) as $lines
  | [$lines[] | select(test("^\\s*[-*] \\[ \\]")) | sub("^\\s*[-*] \\[ \\]\\s*"; "") | row_key]
    + [range(0; $lines | length) as $i
        | $lines[$i]
        | select(test("^\\s*\\|") and (rule | not))
        | select(($lines[$i + 1] // "" | rule) | not)
        | select(test("(?<!\\\\)\\|\\s*(landed|fixed|accepted|runner shift)\\b"; "i") | not)
        | sub("^\\s*\\|\\s*"; "") | [splits("(?<!\\\\)\\|")][0] | gsub("\\\\\\|"; "|") | row_key];

# An item as {line, keys, text}, or null when it is not `- <head> — <text>`
# with at least one backquoted key in its head.
def keyed:
  . as $line
  | (capture("^[-*] (?<head>.+?) —\\s*(?<text>.*)$") // null)
  | if . == null then null
    else [.head | match("`([^`]+)`"; "g") | .captures[0].string] as $keys
    | if ($keys | length) == 0 then null else {line: $line, keys: $keys, text: (.text | sub("\\s+$"; ""))} end
    end;

# The roles a `## Sources` row gives its source (#3594). `oracle` names the
# other system a shallow embedding is compared with (#3964, `design.md` §
# design-scope), whose unit then owes `## Embedding owes`.
def source_roles: ["primary", "secondary", "oracle", "not read"];

# The rows of the body's `## Sources` table (#3594), each as {line, keys,
# role, text}. The table has the columns Source, Role and What it gives. The
# header row and the rule are not rows. The keys are the backquoted spans of
# the first cell, so `` `units.md` § units-issue `` keys `units.md`. The role
# is the second cell, lowercased and unbolded. The text is the third cell. The
# cells are read from the line itself, so a cell held in backquotes keeps them.
# A cell ends at an unescaped `|`, so a `\|` stays inside its cell.
# `source_rows($name)` reads the table of the section `## $name` alike: an
# epic's `## Motivating sources` (#5855) has the columns Source and What it
# gives, so its second cell is its role and its text is empty.
def source_rows($name):
  (section($name) // [])
  | .[]
  | select(test("^\\s*\\|"))
  | . as $line
  | sub("^\\s*\\|"; "") | sub("(?<!\\\\)\\|\\s*$"; "") | [splits("(?<!\\\\)\\|")] | map(gsub("^\\s+|\\s+$"; ""))
  | select(all(test("^:?-+:?$")) | not)
  | select((.[0] // "" | ascii_downcase) != "source")
  | {line: $line,
     keys: [.[0] // "" | match("`([^`]+)`"; "g") | .captures[0].string],
     role: (.[1] // "" | gsub("\\*"; "") | ascii_downcase),
     text: (.[2] // "")};
def source_rows: source_rows("Sources");

# A source's key, as a body cites it (#3158): a `§` after a page's filename
# names a section, and is no part of the key.
def source_key: sub("\\s*§.*$"; "");

# The claim of a design page (#6569, `units.md` § units-issue) in the text of
# a `## Sources` row or a `## Sources read` item: the parts `builds:`,
# `saves:` and `decides:`, each its text up to the next part, with the
# separators between parts trimmed. A part the text does not name is absent.
def claim_labels: ["builds", "saves", "decides"];
def claim_parts:
  . as $text
  | [match("\\b(builds|saves|decides):"; "g") | {label: .captures[0].string, from: .offset, at: (.offset + .length)}] as $marks
  | reduce range(0; $marks | length) as $i ({};
      .[$marks[$i].label] = ($text[$marks[$i].at:($marks[$i + 1].from // ($text | length))] | gsub("^[\\s,;]+|[\\s,;.]+$"; "")));

# What a claim's parts lack, one phrase for each part: absent, empty, `n/a`
# with no reason, or a `saves:` that names no instrument. A part reads
# `n/a — <reason>` where the design claims nothing of it.
def claim_gaps:
  . as $parts
  | [claim_labels[] as $label
      | $parts[$label] as $part
      | if $part == null then "`\($label):` is missing"
        elif $part == "" then "`\($label):` is empty"
        elif $part | test("^n/a\\b") then
          if $part | test("^n/a\\s*—\\s*\\S") then empty else "`\($label):` reads `n/a` with no reason" end
        elif $label == "saves" and ($part | test("\\bread by\\s+\\S") | not) then "`saves:` names no instrument after `read by`"
        else empty
        end];

# Whether the key `.` stands in `$text`, the lines of a `## Sources`: a
# page's filename or a tree path as it is, and `#<issue>` only when no digit
# follows it. A row whose role is `not read` cites its key too, so a seat may
# decline (#3594).
def cited($text):
  source_key as $key
  | if startswith("#") then $text | test("\($key)(?![0-9])")
    else $text | contains($key)
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

# The nine reading axes (`units.md` § units-readings).
def axes: ["univalent", "oracle", "descent", "located", "resident", "rewriting", "zero-cost", "nominal", "general"];

# The question each axis asks of a unit (`units.md` § units-readings), quoted
# where a reading is refused so the writer has it in front of them (#2955).
def questions:
  {univalent: "what univalence and the rewriting core give the construction: an equation, a transported rule, a replayed cell, representation independence",
   oracle: "which part is decided by certificate replay and which is computed; which modality or dominance classifies it",
   descent: "the local data, the interface, the assembly; what a change invalidates and reuses; the parallel width left",
   located: "at which world a judgement or value is meaningful; what crosses worlds or sessions, and by what: by location inside one world (a LAM: region, index, never recycled) or by content across worlds (the CAM: `cam_commit` at the source, `cam_deref` at the destination); whether what crosses is `mobile` (authority) and `Open` (no location pointer)",
   resident: "representation, sharing, persistence; which memory holds the value — a location-addressable store (the runtime's heaps, `core-sequent`'s store) or the content-addressable store (`storage-values`, chunk and content pointer) — and what the crossing between them costs (the boundary and alias classification, the locality bound); where integrity stops and replay decides",
   rewriting: "rules and normal forms; rewrites between rewrites; which coherence tier settles them",
   "zero-cost": "what the change adds at run time and what demands it: a grade above zero, a crossing a located mode names or a branch a session type carries (then it is the program, not overhead), or a recipe policy off by default (then the artifact built without it carries none of its bytes and the checker refuses the forms that need it); what the grade erases; what a hand-written form would cost against it",
   nominal: "what names, freshness, support and renaming give the unit, stated in `theory-nominal-automata`'s terms: which names it binds, allocates, uses or releases and whose identity they keep; its behaviour as a language over an alphabet of allocations, uses and releases, a word or tree automaton with name allocation and deallocation; and which decision it needs of that language: membership, inclusion, emptiness or determinization",
   general: "the level where the unit's result holds: up to homotopy with its coherences, or a shadow of it — homology or another linear form, an analytic or pointwise form, a bounded order or dimension; for a shadow, the general form, the source key that states it and the issue that owes it"};

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

# The concerns of `ledger/concerns.sql` (#2795), each `{id, issue}`: the tasks
# that read the ledger pass its rows as `--argjson concerns`; without the
# argument, the ids as of the landing of `nominal` (#4181), which the
# `check:claims` cases are written against. An id given alone carries no
# issue (#5308).
def concern_rows:
  ($ARGS.named.concerns // ["fork", "nominal", "oracle", "sharing"])
  | map(if type == "string" then {id: ., issue: null} else {id, issue} end);

# The concern ids, in the order the rows give them.
def concerns: concern_rows | map(.id);

# The marks of an issue's `## Concerns` table: per row naming a concern,
# {concern, mark}, the mark `yes` or `no` from a cell reading it alone or
# before its how (`yes — <how>`), or null.
def concern_marks:
  (section("Concerns") // [] | lead)
  | rows
  | .cells as $cells
  | first($cells[] | select(IN(concerns[]))) as $concern
  | {concern: $concern, mark: (first($cells[] | ascii_downcase | capture("^(?<mark>yes|no)\\b").mark) // null)};

# The six rows of a unit's `## Engineering` (`units.md` § units-engineering,
# #5038), in the order the section states them.
def engineering_rows: ["change", "complexity", "latency", "parallelism", "memory", "failure"];

# The rows of an `## Engineering` table, from the section's lines and read
# before its subsections: per row whose first cell names one of the six,
# {row, answer}, the answer the row's last cell with its HTML comments
# dropped, or "" when the row has one cell. So a table `| Row | Bound |` and
# the form's `| Row | Question | Bound |` read alike.
def engineering:
  lead
  | rows
  | (.cells[0] // "" | gsub("\\*"; "") | ascii_downcase) as $row
  | select(IN($row; engineering_rows[]))
  | {row: $row,
     answer: (if (.cells | length) > 1 then .cells[-1] | gsub("(?s)<!--.*?-->"; "") | gsub("^\\s+|\\s+$"; "") else "" end)};

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

# The issue's `## Embedding owes` (#3964): the operations its oracle has and
# gandr lacks, as {empty, none, numbers, malformed}, or null when the body
# has none. A content line, HTML comments and blank lines dropped, is
# `- #n — <the operation>` or `none — <why nothing is owed>`. A bare `none`
# gives no reason, so it is malformed.
def owes_none: test("^\\s*none —\\s*\\S"; "i");
def owes:
  (section("Embedding owes") // null)
  | if . == null then null
    else (join("\n") | gsub("(?s)<!--.*?-->"; "") | split("\n") | map(select(test("\\S")))) as $lines
    | {empty: ($lines | length == 0),
       none: any($lines[]; owes_none),
       numbers: [$lines[] | select(after_item) | capture("^[-*] #(?<n>[0-9]+)").n | tonumber],
       malformed: [$lines[] | select((owes_none or after_item) | not)]}
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

# The issues a body names as its epic (#3398): every `#<n>` on a line opening
# `Advances`, `Part of` or `from:`, in order, once each. Whether each is an
# open `kind:epic` is the caller's read.
def epic_refs:
  [lines[]
    | select(test("^\\s*(Advances|Part of)\\s+#[0-9]|^\\s*from:\\s*#[0-9]"; "i"))
    | scan("(?<![\\w/])#([0-9]+)\\b") | .[0] | tonumber]
  | reduce .[] as $n ([]; if index([$n]) then . else . + [$n] end);

# A unit's identifiers (#7019, `units.md` § units-sources): its number
# `$number`; each number of its `from:` line and of its epic, by
# `epic_refs` and by `$parent`, its parent on GitHub or null; each ledger
# row of `$rows` that the body names in backquotes; and each crate
# directory of `$crates` that the body names as `crates/<dir>` or in
# backquotes, with `gandr-` before it or not.
def unit_identifiers($number; $parent; $rows; $crates):
  . as $body
  | {numbers: ([$number] + ($body | epic_refs) + (if $parent == null then [] else [$parent] end) | unique),
     rows: ([$body | scan("`([a-z0-9][a-z0-9-]*)`") | .[0] | select(IN($rows[]))] | unique),
     crates: ([($body | scan("crates/([a-z0-9][a-z0-9-]*)") | .[0]), ($body | scan("`(?:gandr-)?([a-z0-9][a-z0-9-]*)`") | .[0])]
       | map(select(IN($crates[]))) | unique)};

# The marks by which a design page names one of a unit's identifiers (#7019):
# a number with no digit after it, and a row in backquotes. `test` is the
# expression that jq reads, and `grep` the one that `git grep -E` reads. A
# crate has no mark: its own page stands for it.
def identifier_marks:
  [(.numbers[] | {label: "#\(.)", test: "#\(.)(?![0-9])", grep: "#\(.)([^0-9]|$)"}),
   (.rows[] | {label: "`\(.)`", test: "`\(.)`", grep: "`\(.)`"})];

# Whether a `Where` is spelled as an item path, `crate::path` or a crate
# alone, as rustdoc names it.
def item_path: test("^[A-Za-z_][A-Za-z0-9_]*(::[A-Za-z_][A-Za-z0-9_]*)*$");

# Whether a `Where` is spelled as a repository path: a relative path with a
# `/` or a `.`, and no `::`.
def tree_path: test("^[.A-Za-z0-9_-][^\\s:]*$") and test("[/.]");
