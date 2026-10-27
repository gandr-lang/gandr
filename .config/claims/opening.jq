# Whether `pr:open` opens a body: one line per refusal to print, a `note: `
# line per finding it prints and opens anyway, or nothing.
#
# Input:
#   branch    the branch being opened, `<lane>-<n>-<slug>` when it works an
#             issue
#   body      the body file's text
#   issues    the issues the body works: [{number, body, labels: [name]}]
#   mentions  per key the body supersedes, the tree's lines naming it:
#             {key: ["<path>:<line>:<text>"]}
#   concerns  `ledger/concerns.sql` at the head and at the base:
#             {ids: [id], base: [id], sites: [{concern, crate, module}]}
#   added     the paths the change adds under `crates/*/src/`
#   regressions  the lines the change adds to corpus sources, Rust test files
#             and `.config` cases: [{path, text}]
#   surface   the paths the change touches under `crates/surface-parser/`,
#             `crates/surface-grammar/` and `crates/surface-syntax/`
#   vault     the vault pages and the crates' citations (#2793), or null where
#             no vault checkout is configured: {pages, tree, touched, cited},
#             `pages` and `tree` as `vault.jq` reads them, `touched` the
#             crates whose sources the change touches, `cited` each such
#             crate's `# References` keys at the head
#
# A merge takes the claim off what the body works (`decide.jq`), so the body
# must name it (#2462): a branch that carries an issue number needs
# `Advances #n` or a closing keyword for that issue, and a branch with none
# needs one such line for some issue, the issue the change advances.
#
# The body answers the sources its issues request (#2499): every key an
# issue's `## Sources` names has an item in the body's `## Sources read`, and
# every item there carries a disposition from the vocabulary with its
# evidence. A `supersedes` item is refused while the tree still names the old
# key on a line that does not mark it demoted. An issue's `## Sources` line
# that names no key is noted, not refused.
#
# A primary source that is a vault page is cited where the change decides
# something by it (#2793): when an issue's `## Sources` marks a vault page
# primary and the change touches a crate's sources, each such crate carries a
# `# References` line `` - `vault:<mint>` — <role>: <what it decides> ``, the
# key rule of #2542. A page that decided nothing in the code is marked
# `read: <what it informed>` in `## Sources read`, which answers it.
#
# The body answers every reading axis (#2522, #2955): when an issue it works
# carries a `## Readings`, or the body has one, its `## Readings` table,
# `Family · Axis · Status`, gives each of the six axes one of four forms,
# each with its clause: `answered: <exemplar or site>`, `trivial: <what it
# reduces to>`, `not applicable: <what the change lacks that the axis asks
# about>` or `deferred: #n`. `not selected`, a blank and a bare form are
# refused naming the axis and quoting its question. An axis an issue selects
# `yes` answered other than `answered:` needs a `departed:` item keyed by the
# axis in `## Sources read`. An issue it works whose reading is still the
# migration's `unstated` placeholder, or bare, is refused until the seat
# restates the row on the issue: `claim:next` claims such a unit and prints
# the questions, and the landing is where the restating is required.
#
# The body names each concern it touches (#2523): an item of its
# `## Concerns`, `` - `<id>` — <verdict> ``, names a concern of the ledger
# with `within`, `consolidated: <what merged>` or `new concern: <why none
# fits>`, the last only for a row the change adds. A module or crate the
# change adds whose name is a concern's id, or the last segment of one of its
# sites' modules, belongs to that concern; where every site of it lies in
# another crate, the body declares it `consolidated`, or a `new concern`.
#
# A defect fix lands with what was observed and the check that failed before
# it (#2524): a body closing a `kind:defect` issue `#n` has a non-empty
# `## Observation`, and the change adds a regression naming `#n`: a corpus
# `///` line citing `#n`, a Rust test whose name ends `_n` (or carries `_n_`),
# or a `.config` JSON case whose `"name"` cites `#n`.
#
# A surface form states its parser cost and its demand (#2527): a change to
# the parser, its grammar or its syntax tree (`surface`, the paths it changes
# under `crates/surface-parser/`, `crates/surface-grammar/` or
# `crates/surface-syntax/`) has a `### Surface form` subsection with a
# non-blank `cost:` line (the keystroke scenario's numbers before and after,
# the molder's candidates and windows on the form) and a non-blank
# `demand: <site>` line naming the corpus source or program that needs it.
# The goldens `corpus:goldens` records there follow the corpus and ask for
# none (#2756).

include "targets";
include "sections";
include "vault";

def vocabulary: "`taken: <site>` (the function, test or fixture), `departed: <the recorded design, the change, why>`, `declined: <reason>`, `read: <what it informed>` or `n/a: <reason>`";
def statuses: "`answered: <exemplar or site>`, `trivial: <what it reduces to>`, `not applicable: <what the change lacks that the axis asks about>` or `deferred: #n`";
def answered: test("^(answered|trivial|not applicable):\\s*\\S") or test("^deferred:\\s*#[0-9]+");

# The refusal when the body does not work the branch's issue, or works none.
def claim:
  (.body | targets(working)) as $worked
  | (.branch | capture("^[a-z]+-(?<n>[0-9]+)(-|$)").n // null | if . == null then null else tonumber end) as $n
  | if $n != null then
      if ($worked | index($n)) then empty
      else "the body names no `Advances` or `Closes` line for #\($n), the issue `\(.branch)` names: add `Advances #\($n)` for a slice, or `Closes #\($n)` if it finishes the issue, then run `pr:open` again"
      end
    elif ($worked | length) > 0 then empty
    else "the body names no issue it works: add `Advances #n` for the issue the change advances, or `Closes #n` for one it finishes, then run `pr:open` again"
    end;

# The notes and refusals of `## Sources read` against the issues' `## Sources`.
def sources:
  (.mentions // {}) as $mentions
  | [(.issues // [])[] | .number as $n | (.body | section("Sources") // []) | items | {n: $n, line: ., item: keyed}] as $asked
  | [(.body | section("Sources read") // []) | items] as $read
  | [$read[] | keyed | select(. != null) | .keys[]] as $listed
  | ($asked[] | select(.item == null) | "note: #\(.n)'s `## Sources` line `\(.line)` is not `- `<key>` — <text>`, so no key is read from it"),
    ([$asked[] | select(.item != null) | .n as $n | .item.keys[] | {n: $n, key: .}]
      | map(select(.key as $key | $listed | index($key) | not))
      | unique_by(.key)
      | if length == 0 then empty
        else "the body's `## Sources read` lacks the sources its issue names: add one item per key, `- `<key>` — <disposition>`, the disposition \(vocabulary), then run `pr:open` again:\n" + (map("  - `\(.key)` (#\(.n)'s `## Sources`)") | join("\n"))
        end),
    ($read[]
      | . as $line
      | supersession as $replaced
      | if $replaced != null then
          if $replaced.confirmation == "" then "the `## Sources read` item `\($line)` gives no confirmation: write `- supersedes: `<old key>` — <confirmation>`, then run `pr:open` again"
          else ($mentions[$replaced.old] // [] | map(select(test("demoted"; "i") | not))) as $undemoted
          | if ($undemoted | length) == 0 then empty
            else "the `## Sources read` item `\($line)` supersedes `\($replaced.old)`, and the tree still names it undemoted: remove each reference, or mark it demoted on its line, then run `pr:open` again:\n" + ($undemoted | map("  \(.)") | join("\n"))
            end
          end
        else keyed as $item
        | if $item == null then "the `## Sources read` item `\($line)` names no source: write `- `<key>` — <disposition>`, the disposition \(vocabulary), then run `pr:open` again"
          else ($item.text | capture("^(?<disposition>taken|departed|declined|read|n/a):\\s*(?<evidence>.*)$") // null) as $answer
          | if $answer == null then "the `## Sources read` item `\($line)` has no disposition: end it with \(vocabulary), then run `pr:open` again"
            elif $answer.evidence == "" then "the `## Sources read` item `\($line)` leaves its `\($answer.disposition)` blank: give its evidence, \(vocabulary), then run `pr:open` again"
            else empty
            end
          end
        end);

# The refusals of a primary vault page the crates the change touches leave
# uncited.
def citations:
  .vault as $vault
  | select($vault != null)
  | [(.body | section("Sources read") // []) | items | keyed | select(. != null and (.text | test("^read:\\s*\\S"))) | .keys[]] as $read
  | [(.issues // [])[] | .number as $n | .body | section("Sources") // [] | vault_sources($vault.pages; $vault.tree)
      | select(.primary and .verdict == "resolved") | . + {n: $n}]
  | unique_by(.mint)[]
  | . as $page
  | select(any($read[]; . == $page.name or . == "vault:\($page.mint)") | not)
  | $vault.touched[]
  | . as $crate
  | select(any(($vault.cited[$crate] // [])[]; . == "vault:\($page.mint)") | not)
  | "`crates/\($crate)` cites no `vault:\($page.mint)` (`\($page.name)`), a primary source of #\($page.n), and the change touches its sources: add `- `vault:\($page.mint)` — <exemplar|lineage|background>: <what it decides>` to the `# References` of the module it decides something for, or mark the page `read: <what it informed>` in `## Sources read` if it decided nothing in the code, then run `pr:open` again";

# The refusals of `## Readings`: every axis answered in one of the four forms
# once a unit is worked, and a selected axis left unanswered departed from.
# A unit is worked when an issue the body works has a `## Readings` row
# naming an axis, or the body has a `## Readings` of its own.
def readings:
  [(.issues // [])[] | .number as $n | .body | selected[] | {n: $n, axis: .}] as $asked
  | (any((.issues // [])[]; .body // "" | marks)
      or ((.body | section("Readings")) != null)) as $unit
  | [(.body | section("Sources read") // []) | items | keyed | select(. != null and (.text | test("^departed:\\s*\\S"))) | .keys[]] as $departed
  | [(.body | section("Readings") // [] | lead) | rows | select((.cells[1] // "" | ascii_downcase) != "axis")] as $rows
  | ($rows[]
      | select(.cells[1] // "" | IN(axes[]) | not)
      | "the `## Readings` row `\(.line)` names no axis: its second cell is one of `\(axes | join("`, `"))`, then run `pr:open` again"),
    (select($unit)
      | [axes[]
          | . as $axis
          | [$rows[] | select(.cells[1] == $axis)] as $mine
          | if ($mine | length) == 0 then "  - `\($axis)`, no row: \(questions[$axis])"
            elif ([$mine[] | select(.cells[2] // "" | answered)] | length) == 0 then "  - `\($axis)`, \($mine[0].cells[2] // "" | if . == "" then "blank" else "`\(.)`" end): \(questions[$axis])"
            else empty
            end]
      | if length == 0 then empty
        else "the body's `## Readings` leaves an axis unanswered: give each one \(statuses), the clause naming what the axis asks (never `not selected`, a blank or a bare form), then run `pr:open` again:\n" + join("\n")
        end),
    (select($unit)
      | [axes[]
          | . as $axis
          | select(any($asked[]; .axis == $axis))
          | select(any($rows[]; .cells[1] == $axis and (.cells[2] // "" | answered)))
          | select(any($rows[]; .cells[1] == $axis and (.cells[2] // "" | test("^answered:"))) | not)
          | select($departed | index($axis) | not)
          | "  - `\($axis)` (#\(first($asked[] | select(.axis == $axis)).n)'s `## Readings`)"]
      | if length == 0 then empty
        else "an axis the issue selects is answered other than `answered:`: add `- `<axis>` — departed: <the recorded design, the change, why>` to `## Sources read` for each, then run `pr:open` again:\n" + join("\n")
        end),
    ((.issues // [])[]
      | .number as $n
      | [.body // "" | marks | select(.mark != null and (.reason == null or (.reason | unstated)))] as $unstated
      | select($unstated | length > 0)
      | "#\($n)'s `## Readings` still leaves an axis unstated: restate each row on the issue as `yes — <what it gives this unit>` or `no — <why it does not reach it>`, then run `pr:open` again:\n"
        + ([axes[] | . as $axis | select(any($unstated[]; .axis == $axis)) | "  - `\($axis)`: \(questions[$axis])"] | join("\n")));

# An added source path's module as {path, crate, name}: its last segment, or
# for a crate root the crate's name past its category; null for a test file
# or a path outside a crate's `src`.
def addition:
  . as $path
  | (capture("^crates/(?<crate>[^/]+)/src/(?<rest>.+)\\.rs$") // null)
  | if . == null or (.rest | test("(^|/)tests(/|$)")) then null
    else .crate as $crate
    | (.rest | sub("/mod$"; "")) as $rest
    | {path: $path, crate: $crate, name: (if $rest == "lib" or $rest == "main" then $crate | sub("^[a-z]+-"; "") else $rest | split("/") | last end)}
    end;

# The refusals of `## Concerns` against the ledger and the modules added.
def concerns:
  (.concerns // {ids: [], base: [], sites: []}) as $ledger
  | "`within`, `consolidated: <what merged>` or `new concern: <why none fits>`" as $verdicts
  | "`\($ledger.ids | join("`, `"))`" as $known
  | [(.body | section("Concerns") // []) | items] as $items
  | [$items[] | keyed | select(. != null) | . as $item | .keys[]
      | . as $key
      | {key: $key, line: $item.line, known: ($ledger.ids | index($key) != null), had: ($ledger.base | index($key) != null),
         verdict: ($item.text | if test("^within\\b") then "within" elif test("^consolidated:\\s*\\S") then "consolidated" elif test("^new concern:\\s*\\S") then "new concern" else null end)}] as $named
  | ($items[] | select(keyed == null) | "the `## Concerns` item `\(.)` names no concern: write `- `<id>` — <verdict>`, the verdict \($verdicts), then run `pr:open` again"),
    ($named[]
      | if .verdict == null then "the `## Concerns` item `\(.line)` gives `\(.key)` no verdict: end it with \($verdicts), then run `pr:open` again"
        elif .verdict == "new concern" and (.known | not) then "the `## Concerns` item `\(.line)` declares `\(.key)` a new concern, and `ledger/concerns.sql` has no row for it: add the row in this change, then run `pr:open` again"
        elif .verdict == "new concern" and .had then "the `## Concerns` item `\(.line)` declares `\(.key)` a new concern, and `ledger/concerns.sql` already had it: write `within` or `consolidated: <what merged>`, then run `pr:open` again"
        elif .known | not then "the `## Concerns` item `\(.line)` names `\(.key)`, no concern of `ledger/concerns.sql`: name one of \($known), or add its row as a `new concern`, then run `pr:open` again"
        else empty
        end),
    ([$named[] | select(.verdict == "new concern" and .known and (.had | not))] | length > 0) as $new
    | (.added // [])[]
    | addition
    | select(. != null)
    | . as $added
    | ([$ledger.ids[] | select(. == $added.name)] + [$ledger.sites[] | select(.module != "" and (.module | split("::") | last) == $added.name) | .concern] | unique)[]
    | . as $concern
    | [$ledger.sites[] | select(.concern == $concern)] as $sites
    | select(([$sites[].crate] | index($added.crate)) == null)
    | select($new or ([$named[] | select(.key == $concern and .verdict == "consolidated")] | length > 0) | not)
    | "the change adds `\($added.path)`, a module of the concern `\($concern)`, whose sites lie in \($sites | map("`\(.crate)\(if .module == "" then "" else "::\(.module)" end)`") | join(", ")): declare `- `\($concern)` — consolidated: <what merged>` in `## Concerns`, or a `new concern` with its row, then run `pr:open` again";

# Whether an added line `{path, text}` is a regression naming issue `$n`.
def regression($n):
  ($n | tostring) as $n
  | if (.path | endswith(".gandr")) then .text | test("^\\s*///.*#\($n)\\b")
    elif (.path | endswith(".rs")) then .text | test("\\bfn\\s+\\w*_\($n)(_\\w*)?\\s*[(<]")
    elif (.path | startswith(".config/") and endswith(".json")) then .text | test("\"name\":\\s*\"[^\"]*#\($n)\\b")
    else false
    end;

# The refusals of a defect fix missing its observation or its regression.
def defects:
  (.body | targets(closing)) as $closed
  | (.regressions // []) as $added
  | (.body | section("Observation") // [] | filled) as $observed
  | (.issues // [])[]
  | select((.labels // []) | index("kind:defect"))
  | .number as $n
  | select($closed | index($n))
  | [if $observed then empty else "`## Observation`: the instrument used (a debugger, a trace, a failing fixture) and the value read there" end,
     if ([$added[] | select(regression($n))] | length) > 0 then empty
     else "a regression naming #\($n): a corpus `///` line citing it, a Rust test named `…_\($n)`, or a `.config` case whose name cites it, added by the change" end]
  | select(length > 0)
  | "the body closes #\($n), a `kind:defect`, without \(join(", and without ")); add \(if length > 1 then "both" else "it" end), then run `pr:open` again";

# The lines of the body's `### $name` subsection, up to the next heading of
# level two or three, or null when it has none.
def subsection($name):
  lines as $lines
  | ([range(0; $lines | length) | select($lines[.] | test("^### \($name)\\s*$"))] | first) as $start
  | if $start == null then null
    else $lines[$start + 1:] as $rest
    | ([range(0; $rest | length) | select($rest[.] | test("^###? "))] | first // ($rest | length)) as $end
    | $rest[:$end]
    end;

# A golden `corpus:goldens` records for the corpus: a source's role golden
# and the `unexercised.roles` list under `crates/surface-grammar/`, and its
# recovery record under `crates/surface-parser/`. It follows the corpus, not
# the parser.
def golden:
  test("^crates/surface-grammar/tests/highlight/.+\\.roles$")
  or test("^crates/surface-parser/tests/recovery/.+\\.recovery$");

# The refusal of a change to the parser whose body states no surface form.
def surface:
  (.surface // [] | map(select(golden | not))) as $paths
  | select($paths | length > 0)
  | (.body | subsection("Surface form")) as $form
  | ($form // [] | map(select(test("^\\s*(?:[-*]\\s+)?(?:\\*\\*)?cost:(?:\\*\\*)?\\s*\\S")))) as $cost
  | ($form // [] | map(select(test("^\\s*(?:[-*]\\s+)?(?:\\*\\*)?demand:(?:\\*\\*)?\\s*\\S")))) as $demand
  | [if $form == null then "a `### Surface form` subsection" else empty end,
     if $cost == [] then "a non-blank `cost:` line (the keystroke scenario's numbers before and after, the molder's candidates and windows on the form)" else empty end,
     if $demand == [] then "a non-blank `demand: <site>` line naming the corpus source or program that needs the form" else empty end]
  | select(length > 0)
  | "the change touches the parser (\($paths[:3] | map("`\(.)`") | join(", "))\(if ($paths | length) > 3 then ", …" else "" end)) and the body lacks \(join(", and ")) (#2527); add it, then run `pr:open` again";

claim, sources, citations, readings, concerns, defects, surface
