# Whether `pr:open` opens a body: one line per refusal to print, a `note: `
# line per finding it prints and opens anyway, or nothing.
#
# Input:
#   branch    the branch being opened, `<lane>-<n>-<slug>` when it works an
#             issue, or `<lane>-<seat>-<n>-<slug>` from a numbered seat; the
#             slug opens with a letter
#   body      the body file's text
#   issues    the issues the body works: [{number, body, labels: [name]}]
#   mentions  per key the body supersedes, the tree's lines naming it:
#             {key: ["<path>:<line>:<text>"]}
#   concerns  `ledger/concerns.sql` at the head and at the base:
#             {ids: [id], base: [id], sites: [{concern, crate, module}]}
#   added     the paths the change adds under `crates/*/src/`
#   held      the modules of `added` that a crate of the base already holds,
#             each as its path below `src`, no `.rs` and no `/mod` (#7055)
#   regressions  the lines the change adds to corpus sources, Rust test files,
#             `.config` cases and `contrib/` TypeScript: [{path, text}]
#   surface   the paths the change touches under `crates/surface-parser/`,
#             `crates/surface-grammar/` and `crates/surface-syntax/`
#   spelled   the issues that a `spelling: replaces` line of the body cites
#             and that stand open (#6876): [n]
#   vault     the vault pages and the crates' citations (#2793), or null where
#             no vault checkout is configured: {pages, tree, touched, cited},
#             `pages` and `tree` as `vault.jq` reads them, `touched` the
#             crates whose sources the change touches, `cited` each such
#             crate's `# References` keys at the head
#   ceilings  the ceilings the change adds (`ceilings.bash`, #5039), each
#             with the cited issues still open:
#             [{path, line, kind, text, cites: [n], open: [n]}]
#   budget    the `gh` call sites the change alters (`.config/gh/changed.bash`,
#             #5061): [{file, scope, api}]
#   comments  the comment lines the change removes (`comments.bash`, #6004),
#             one row per source: [{path, removed, dropped}]
#   views     what the change builds that a consumer sees and where the body
#             says the consumer sees it (`views.bash`, #6873):
#             {built: [name], tests: [{surface, test, found}]}
#
# A merge reads the claims of what the body works (`decide.jq`), so the body
# must name it (#2462): a branch that carries an issue number needs
# `Advances #n` or a closing keyword for that issue, and a branch with none
# needs one such line for some issue, the issue the change advances.
#
# The body answers the sources its issues request (#2499): every key an
# issue's `## Sources` names has an item in the body's `## Sources read`, and
# every item there carries a disposition from the vocabulary with its
# evidence. A `supersedes` item is refused while the tree still names the old
# key on a line that does not mark it demoted. An issue's `## Sources` row
# that names no key, or a `## Sources` written as a list, is noted, not
# refused (#3594). An issue's row that states a design's claim, `builds:`,
# `saves:` and `decides:` (#6569), is answered by an item that names the site
# of each part, or by `departed:` with its reason.
#
# A primary source that is a vault page is cited where the change decides
# something by it (#2793), and only there (#4096): when an issue's
# `## Sources` marks a vault page primary and the change touches a crate's
# sources, the crate carries a `# References` line
# `` - `vault:<mint>` — <role>: <what it decides> ``, the key rule of #2542,
# or the body names it under the page's `## Sources read` item as
# `  - read in: crates/<a>, crates/<b> — <what the change does there>`, where
# the change touches the crate and the page decides nothing in it. A page that
# decided nothing in the code is marked `read: <what it informed>` in
# `## Sources read`, which answers it for every crate.
#
# The body answers every reading axis (#2522, #2955): when an issue it works
# carries a `## Readings`, or the body has one, its `## Readings` table,
# `Family · Axis · Status`, gives each of the nine axes one of four forms,
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
# `// - see: #n` or `/// - see: #n` line in a source's references (#4900,
# #6071), a Rust test whose
# name ends `_n` (or carries `_n_`), a `.config` JSON case whose `"name"`
# cites `#n`, a case of a `.config` shell script named `*cases.bash` whose
# `fail "#n: …"` message names it (#4421), or, in an editor extension's
# TypeScript tests (`contrib/` files named `*.test.ts` or under a `smoke/`
# directory), a `//` line or a `test(…)` name citing `#n` (#3538).
#
# A surface form states its parser cost and its demand (#2527): a change to
# the parser, its grammar or its syntax tree (`surface`, the paths it changes
# under `crates/surface-parser/`, `crates/surface-grammar/` or
# `crates/surface-syntax/`) has a `### Surface form` subsection with a
# non-blank `cost:` line (the keystroke scenario's numbers before and after,
# the molder's candidates and windows on the form) and a non-blank
# `demand: <site>` line naming the corpus source or program that needs it.
# It states its spelling too (#6876), since the owner's rule of 2026-11-11
# admits one spelling for each form: `spelling: sole`, or `spelling: replaces
# <old>, refused here` where the change refuses the old spelling, or
# `spelling: replaces <old>, refused by #n` where `#n` is an open issue.
# The goldens `corpus:goldens` records there follow the corpus and ask for
# none (#2756).
#
# A closing keyword closes only from the head's keyword lines (#2980): one
# anywhere else (`closed #628` in prose, a `Closes #n` line with prose after
# it or below a heading) is refused, since GitHub closes the issue it names
# when the pull request merges (`targets.jq`'s `strays`).
#
# Every body answers `## Refactoring` (#2884): from what the change did and
# learned, is a refactoring justified? Its first line is `yes`, `maybe` or
# `no`; a `yes` or `maybe` lists a table `| Kind | Where | Observation |`,
# each kind one of `refactor_kinds` and each `Where` an item path or a
# repository path, which `check:refactoring` resolves.
#
# A landing on a `collector` names the rows it clears (#3326): the guard
# closes the collector once no row is open, so the body `Advances #n` and
# never closes it, and its `## Rows` lists the rows the change clears, one
# item `` - `<row>` `` per row, keyed as the collector keys it
# (`collector_rows`). An empty or missing `## Rows`, or an item naming no
# open row of the collector, is refused.
#
# A body answers its issues' `## Engineering` with measured numbers (#5039,
# `units.md` § units-pr): when an issue it works has the section, the body has
# one, and each row the issue states with a bound has its answer there. The
# answer is neither empty nor `n/a`. Each row but `failure` carries a number,
# the measurement, or the issue naming the serial step. A row the issue marks
# `n/a — <reason>` may answer `n/a`, or stay out.
#
# A ceiling the change adds cites the open issue that removes it (#5039): a
# `spec_clause_traversal` waiver or an `economy:` comment carries `#<n>` in
# its extent, and one such issue is open. A reason string alone is refused
# with its file and line.
#
# A change that drops many comment lines states the facts it keeps (#6004):
# when the sources under `corpus/`, `library/` and `crates/` drop
# `facts_threshold` comment lines or more that the change does not add back,
# the body has `## Facts kept`. Its table `| Source | Claim | Class | Where it
# lands |` has one row for each claim the rewrite drops, or the section says
# `none — <reason>`. Each row's class is `needed`, `noise` or `borderline`. A
# `needed` row names where its claim lands, a `noise` row why it stays out,
# and a `borderline` row its finding on #2917. A missing section, a row with
# no class, and a row with no fourth cell for its class are refused.
#
# Each speedup claim states its corpus and its algorithmic baseline (#3479,
# the algorithm-first ruling of #320): a line that claims a factor, a
# percentage or a speedup carries `corpus: <the inputs the number is over>`
# and `baseline: <the algorithm it is measured against>`. The check reads the
# body alone, outside its code blocks and HTML comments, and refuses a claim
# that lacks either.

include "targets";
include "sections";
include "vault";

def vocabulary: "`taken: <site>` (the function, test or fixture), `departed: <the recorded design, the change, why>`, `declined: <reason>`, `read: <what it informed>` or `n/a: <reason>`";
def statuses: "`answered: <exemplar or site>`, `trivial: <what it reduces to>`, `not applicable: <what the change lacks that the axis asks about>` or `deferred: #n`";
def answered: test("^(answered|trivial|not applicable):\\s*\\S") or test("^deferred:\\s*#[0-9]+");

# The refusal when the body does not work the branch's issue, or works none.
def claim:
  (.body | targets(working)) as $worked
  | (.branch | capture("^[a-z]+(-[0-9]+)?-(?<n>[0-9]+)(-[a-z]|$)").n // null | if . == null then null else tonumber end) as $n
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
  | [(.issues // [])[] | .number as $n | .body | source_rows | {n: $n, line, keys}] as $asked
  | [(.issues // [])[] | select([.body | section("Sources") // [] | items] | length > 0) | .number] as $listed_form
  | [(.body | section("Sources read") // []) | items] as $read
  | [$read[] | keyed | select(. != null) | .keys[]] as $listed
  | ($listed_form[] | "note: #\(.)'s `## Sources` is a list, so no key is read from it: write it as the table `| Source | Role | What it gives |`"),
    ($asked[] | select(.keys == []) | "note: #\(.n)'s `## Sources` row `\(.line)` names no source in backquotes, so no key is read from it"),
    ([$asked[] | .n as $n | .keys[] | {n: $n, key: .}]
      | map(select(.key as $key | $listed | index($key) | not))
      | unique_by(.key)
      | if length == 0 then empty
        else "the body's `## Sources read` lacks the sources its issue names: add one item per key, `- `<key>` — <disposition>`, the disposition \(vocabulary), then run `pr:open` again:\n" + (map("  - `\(.key)` (#\(.n)'s `## Sources`)") | join("\n"))
        end),
    ([(.issues // [])[] | .number as $n | .body | source_rows
        | select(.text | claim_parts | length > 0)
        | {n: $n, keys}]
      | .[] as $claim
      | [$read[] | keyed | select(. != null and any(.keys[]; IN($claim.keys[])))] as $items
      | select($items | length > 0)
      | select(any($items[]; .text | test("^departed:\\s*\\S")) | not)
      | ([$items[] | .text | claim_parts] | add // {}) as $parts
      | [claim_labels[] | select(($parts[.] // "") == "")] as $missing
      | select($missing | length > 0)
      | "the `## Sources read` item of `\($claim.keys | join("`, `"))` does not answer the claim that #\($claim.n)'s `## Sources` states (`units.md` § units-pr): name the site of \($missing | map("`\(.):`") | join(", ")) in it, as `taken: builds: <site>, saves: <site>, decides: <site>`, or write `departed: <the recorded design, the change, why>`, then run `pr:open` again"),
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

# The crates each `## Sources read` item names `read in:` under it, as
# {under, crates}: `under` the item's keys, `crates` each `crates/<name>` the
# nested line names. A nested line with no account after its `—` names none.
def read_in:
  (section("Sources read") // [])
  | reduce .[] as $line ({under: [], found: []};
      if $line | test("^[-*] ") then .under = (($line | keyed) // {keys: []} | .keys)
      else ($line | capture("^\\s+[-*] read in:\\s*(?<crates>.+?)\\s+—\\s*(?<what>\\S.*)$") // null) as $named
      | if $named == null then .
        else .found += [{under, crates: [$named.crates | match("crates/([A-Za-z0-9_-]+)"; "g") | .captures[0].string]}]
        end
      end)
  | .found;

# The refusals of a primary vault page the crates the change touches leave
# uncited and name nowhere under the page.
def citations:
  .vault as $vault
  | select($vault != null)
  | [(.body | section("Sources read") // []) | items | keyed | select(. != null and (.text | test("^read:\\s*\\S"))) | .keys[]] as $read
  | (.body | read_in) as $read_in
  | [(.issues // [])[] | .number as $n | .body | [source_rows] | vault_sources($vault.pages; $vault.tree)
      | select(.primary and .verdict == "resolved") | . + {n: $n}]
  | unique_by(.mint)[]
  | . as $page
  | select(any($read[]; . == $page.name or . == "vault:\($page.mint)") | not)
  | $vault.touched[]
  | . as $crate
  | select(any(($vault.cited[$crate] // [])[]; . == "vault:\($page.mint)") | not)
  | select(any($read_in[]; any(.under[]; . == $page.name or . == "vault:\($page.mint)") and any(.crates[]; . == $crate)) | not)
  | "`crates/\($crate)` cites no `vault:\($page.mint)` (`\($page.name)`), a primary source of #\($page.n), and the change touches its sources: add `- `vault:\($page.mint)` — <newest|dependency|anchor|exemplar>: <what it decides>` to the `# References` of the module it decides something for, or name the crate under the page's `## Sources read` item as `  - read in: crates/\($crate) — <what the change does there>` if the page decided nothing there, or mark the page `read: <what it informed>` if it decided nothing in the code, then run `pr:open` again";

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

# An added source path's module as {path, crate, rest, root, name}: `rest` is
# its path below `src`, no `.rs` and no `/mod`; `name` its last segment, or for
# a crate root the crate's name past its category; null for a test file or a
# path outside a crate's `src`.
def addition:
  . as $path
  | (capture("^crates/(?<crate>[^/]+)/src/(?<rest>.+)\\.rs$") // null)
  | if . == null or (.rest | test("(^|/)tests(/|$)")) then null
    else .crate as $crate
    | (.rest | sub("/mod$"; "")) as $rest
    | ($rest == "lib" or $rest == "main") as $root
    | {path: $path, crate: $crate, rest: $rest, root: $root, name: (if $root then $crate | sub("^[a-z]+-"; "") else $rest | split("/") | last end)}
    end;

# The refusals of `## Concerns` against the ledger and the modules added. A
# module that a crate of the base already holds at its path moves, and adds
# nothing to a concern (#7055); a crate root is always new.
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
    | (.held // []) as $held
    | (.added // [])[]
    | addition
    | select(. != null and (.root or (.rest | IN($held[]) | not)))
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
  | if (.path | endswith(".gandr")) then .text | test("^\\s*///?\\s*- see: #\($n)\\b")
    elif (.path | endswith(".rs")) then .text | test("\\bfn\\s+\\w*_\($n)(_\\w*)?\\s*[(<]")
    elif (.path | startswith(".config/") and endswith(".json")) then .text | test("\"name\":\\s*\"[^\"]*#\($n)\\b")
    elif (.path | startswith(".config/") and endswith("cases.bash")) then .text | test("\\bfail\\s+\"#\($n):")
    elif (.path | startswith("contrib/") and (endswith(".test.ts") or test("/smoke/[^/]+\\.ts$")))
    then .text | test("^\\s*//.*#\($n)\\b|\\btest\\(\\s*[\"'`][^\"'`]*#\($n)\\b")
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
     else "a regression naming #\($n): a corpus `// - see: #\($n)` or `/// - see: #\($n)` line, a Rust test named `…_\($n)`, a `.config` case whose name cites it, or a `//` line or `test(…)` name citing it in an extension's TypeScript tests, added by the change" end]
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

# A golden `corpus:goldens` records for the corpus: a source's role golden,
# a headline source's hover golden and the `unexercised.roles` list under
# `crates/surface-grammar/`, and its recovery record under
# `crates/surface-parser/`. It follows the corpus, not the parser.
def golden:
  test("^crates/surface-grammar/tests/highlight/.+\\.(?:roles|hover)$")
  or test("^crates/surface-parser/tests/recovery/.+\\.recovery$");

# The refusals of a change to the parser whose body states no surface form,
# or a spelling in none of its three forms, or an old spelling whose unit
# does not stand open (#6876).
def surface:
  (.surface // [] | map(select(golden | not))) as $paths
  | select($paths | length > 0)
  | (.spelled // []) as $open
  | (.body | subsection("Surface form")) as $form
  | ($form // [] | map(select(test("^\\s*(?:[-*]\\s+)?(?:\\*\\*)?cost:(?:\\*\\*)?\\s*\\S")))) as $cost
  | ($form // [] | map(select(test("^\\s*(?:[-*]\\s+)?(?:\\*\\*)?demand:(?:\\*\\*)?\\s*\\S")))) as $demand
  | [$form // [] | .[] | capture("^\\s*(?:[-*]\\s+)?(?:\\*\\*)?spelling:(?:\\*\\*)?\\s*(?<form>\\S.*)$").form] as $spelling
  | "`spelling: sole`, `spelling: replaces <old>, refused here` or `spelling: replaces <old>, refused by #n`" as $forms
  | ([if $form == null then "a `### Surface form` subsection" else empty end,
      if $cost == [] then "a non-blank `cost:` line (the keystroke scenario's numbers before and after, the molder's candidates and windows on the form)" else empty end,
      if $demand == [] then "a non-blank `demand: <site>` line naming the corpus source or program that needs the form" else empty end,
      if $spelling == [] then "a `spelling:` line, \($forms) (#6876)" else empty end]
     | select(length > 0)
     | "the change touches the parser (\($paths[:3] | map("`\(.)`") | join(", "))\(if ($paths | length) > 3 then ", …" else "" end)) and the body lacks \(join(", and ")) (#2527); add it, then run `pr:open` again"),
    ($spelling[]
     | select(test("^sole\\b") or test("^replaces\\s+\\S.*,\\s*refused\\s+(here|by\\s+#[0-9]+)\\b") | not)
     | "the line `spelling: \(.)` states none of the three forms, \($forms) (#6876); write one of them, then run `pr:open` again"),
    ($spelling[]
     | capture("^replaces\\s+\\S.*,\\s*refused\\s+by\\s+#(?<n>[0-9]+)\\b").n
     | tonumber
     | select(IN($open[]) | not)
     | "the line `spelling: replaces …, refused by #\(.)` names #\(.), which does not stand open: name the open unit that refuses the old spelling, or refuse it in this change and write `refused here`, then run `pr:open` again");

# The refusals of a body working a `collector` (#3326): closed by a keyword,
# or advanced without `## Rows` naming its open rows.
def collectors:
  (.body | targets(closing)) as $closed
  | [(.body | section("Rows") // []) | items | sub("^[-*]\\s+"; "") | row_key] as $named
  | (.issues // [])[]
  | select((.labels // []) | index("collector"))
  | .number as $n
  | (.body // "" | collector_rows) as $open
  | if ($closed | index($n)) then "the body closes #\($n), a `collector`: its guard closes it once no row is open, so write `Advances #\($n)` and list the rows the change clears under `## Rows`, then run `pr:open` again"
    elif ($named | length) == 0 then "the body advances #\($n), a `collector`, and names no row it clears: add `## Rows` with one item `` - `<row>` `` per row of #\($n) the change clears, keyed as #\($n) keys it, then run `pr:open` again"
    else $named[] | select(. as $row | $open | index($row) | not)
    | "the `## Rows` item `\(.)` names no open row of #\($n)\(if ($open | length) == 0 then ", which has none" else " (`\($open[:8] | join("`, `"))`\(if ($open | length) > 8 then ", …" else "" end))" end): name the rows the change clears as #\($n) keys them, then run `pr:open` again"
    end;

# The refusal of a closing keyword outside the head's keyword lines (#2980):
# GitHub would close the issue it names on merge, and `pr:open` and the claim
# lifecycle read it as a closing target even quoted as code.
def keywords:
  .body | strays[]
  | "the body's line `\(.line)` carries `\(.keyword)`, a closing keyword: unquoted, GitHub closes the issue it names when the pull request merges, and `pr:open` and the claim lifecycle take it as closed even quoted. Name the issue without the verb (`#628 was closed by the epics workflow`), or close it on a `Closes #n` line at the head, then run `pr:open` again";

# The refusals of a change that builds a view or closes a `view` unit
# (#6873). A change that adds a request or a card type builds a view, so the
# issue it closes carries `view`. A body that closes a `view` issue holds a
# row of `## Observed at` whose test stands at HEAD under the paths of its
# shipped surface (`views.bash`). A body that only advances the issue passes.
def viewed:
  (.body | targets(closing)) as $closed
  | (.views // {built: [], tests: []}) as $views
  | [(.issues // [])[] | select(.number as $n | $closed | index($n))] as $closing
  | [$closing[] | select((.labels // []) | index("view"))] as $viewing
  | (if ($views.built | length) > 0 and ($closing | length) > 0 and ($viewing | length) == 0 then
       "the change adds \($views.built | join(", ")), a view, and closes \($closing | map("#\(.number)") | join(", ")), which carries no `view`: label the issue `view` and write its `## Observed at`, or write \($closing | map("`Advances #\(.number)`") | join(" and ")) while the view stands on its server side alone, then run `pr:open` again"
     else empty end),
    ($viewing[]
      | .number as $n
      | select(any($views.tests[]; .found) | not)
      | ($views.tests | map("`\(.surface)` `\(.test)`") | join(", ")) as $read
      | "the body closes #\($n), a `view` unit, and no row of its `## Observed at` names a shipped surface whose test stands at the head\(if $read == "" then "" else " (none found: \($read))" end): write `| Surface | How to reach it | Test |` with a test under the surface's paths in `.config/bodies/surfaces.json`, or write `Advances #\($n)` while the view stands on its server side alone, then run `pr:open` again");

# The refusals of `## Refactoring` (#2884): the section present, its first
# line one verdict, `yes`, `maybe` or `no`, and a `yes` or `maybe` answered
# by a table, `| Kind | Where | Observation |`, each row a kind of
# `refactor_kinds`, one or more `Where`, each an item path or a repository
# path, and an observation; a `no` lists none. `check:refactoring` resolves
# each `Where` against the workspace.
def refactorings:
  "`| Kind | Where | Observation |`" as $table
  | "`\(refactor_kinds | join("`, `"))`" as $kinds
  | (.body | refactoring) as $section
  | if $section == null then "the body lacks `## Refactoring`: from what this change did and learned, is a refactoring justified? Write the section with its first line `yes`, `maybe` or `no`, and for `yes` or `maybe` a table \($table), each kind one of \($kinds), then run `pr:open` again"
    elif $section.verdict == null then "the body's `## Refactoring` opens on no verdict: its first line is `yes`, `maybe` or `no`, alone or before ` — <clause>`, then run `pr:open` again"
    elif $section.verdict == "no" then
      ($section.rows[] | "the body's `## Refactoring` says `no` and lists the row `\(.line)`: keep the rows and say `yes` or `maybe`, or `no` alone, then run `pr:open` again")
    elif ($section.rows | length) == 0 then "the body's `## Refactoring` says `\($section.verdict)` and has no row: add a table \($table) naming what this change found, then run `pr:open` again"
    else
      $section.rows[]
      | (select(.kind | IN(refactor_kinds[]) | not)
          | "the `## Refactoring` row `\(.line)` names the kind `\(.kind)`: write one of \($kinds), then run `pr:open` again"),
        (select(.whereas == [])
          | "the `## Refactoring` row `\(.line)` names no `Where`: name each item the change read or touched as `crate::path`, or a repository path, then run `pr:open` again"),
        (.line as $line | .whereas[] | select((item_path or tree_path) | not)
          | "the `## Refactoring` row `\($line)` names `\(.)`, neither an item path (`crate::path`) nor a repository path, then run `pr:open` again"),
        (select(.observation | test("\\S") | not)
          | "the `## Refactoring` row `\(.line)` gives no observation: say what this change found there, then run `pr:open` again")
    end;

# The refusals of the body's `## Engineering` against the sections of the
# issues it works (#5039): the section missing, or a row an issue states with
# a bound left out, empty, `n/a`, or with no number where one is measured. A
# `streaming` row holds two times, the first result and the whole (#6884).
def engineering_answers:
  def na: test("^n/?a\\b"; "i");
  def times: [scan("[0-9]+(?:[.,][0-9]+)?\\s*(?:ns|µs|us|ms|s|sec|seconds?|min|minutes?|h)\\b")] | length;
  [(.issues // [])[] | .number as $n | (.body // "" | section("Engineering")) as $lines
    | select($lines != null) | $lines | engineering | {n: $n, row, bound: (.answer | na | not)}] as $asked
  | select($asked | length > 0)
  | (.body | section("Engineering")) as $section
  | "with its measured number (`units.md` § units-pr)" as $form
  | if $section == null then
      "the body lacks `## Engineering`, which \([$asked[].n] | unique | map("#\(.)") | join(", ")) states: answer each row the issue states with a bound \($form), then run `pr:open` again"
    else [$section | engineering] as $rows
    | $asked
    | map(select(.bound))
    | unique_by(.row)[]
    | . as $ask
    | [$rows[] | select(.row == $ask.row) | .answer] as $answers
    | if ($answers | length) == 0 then "the body's `## Engineering` has no row `\($ask.row)`, which #\($ask.n) states with a bound: answer it \($form), then run `pr:open` again"
      elif all($answers[]; . == "") then "the body's `## Engineering` leaves `\($ask.row)` empty, which #\($ask.n) states with a bound: answer it \($form), then run `pr:open` again"
      elif all($answers[]; na) then "the body's `## Engineering` answers `\($ask.row)` with `n/a`, and #\($ask.n) states it with a bound: answer it \($form), then run `pr:open` again"
      elif $ask.row == "streaming" and all($answers[]; times < 2) then "the body's `## Engineering` answers `streaming` with fewer than two times: report the time to the first result beside the time of the whole, before and after (`units.md` § units-engineering), then run `pr:open` again"
      elif $ask.row != "failure" and all($answers[]; test("[0-9]") | not) then "the body's `## Engineering` answers `\($ask.row)` with no number: report the measurement, or the issue that names the serial step (`units.md` § units-engineering), then run `pr:open` again"
      else empty
      end
    end;

# The refusals of a ceiling the change adds without an open issue that
# removes it (#5039), each with its file and line.
def ceilings:
  (.ceilings // [])[]
  | (if .kind == "waiver" then "a `spec_clause_traversal` waiver" else "an `economy:` ceiling" end) as $what
  | (if .kind == "waiver" then "its `reason`" else "its comment" end) as $where
  | if (.cites | length) == 0 then
      "`\(.path):\(.line)` adds \($what) that cites no issue (`\(.text)`): a ceiling cites the open issue that removes it, so write `#<n>` in \($where) (`units.md` § units-engineering), then run `pr:open` again"
    elif (.open | length) == 0 then
      "`\(.path):\(.line)` adds \($what) that cites \(.cites | map("#\(.)") | join(", ")), and none is open: cite the open issue that removes the ceiling in \($where), then run `pr:open` again"
    else empty
    end;

# The refusals of a change that alters a `gh` call site and does not price
# it under `## API budget` (#5061). A line of the section prices a site when
# it names the site in backquotes, by its scope or, for a call at a file's
# top level, by its file, and names the measure: `rateLimit` for a GraphQL
# cost, `call log` for the router's log, `REST` for one request a call, or
# `rate_limit` for the free gauge.
def api_budget:
  (.budget // []) as $altered
  | select($altered | length > 0)
  | (.body | section("API budget")) as $section
  | "a line that names it in backquotes and its measure: `rateLimit`, `call log`, `REST` or `rate_limit`" as $form
  | if $section == null then
      "the body lacks `## API budget`, and the change alters \($altered | length) `gh` call site\(if ($altered | length) == 1 then "" else "s" end): price each with \($form), then run `pr:open` again:\n\($altered | map("  - `\(if .scope == "-" then .file else .scope end)` (\(.file), \(.api))") | join("\n"))"
    else $altered[]
    | (if .scope == "-" then .file else .scope end) as $name
    | select(any($section[]; index("`\($name)`") != null and test("rateLimit|call log|\\bREST\\b|rate_limit")) | not)
    | "the body's `## API budget` does not price `\($name)` (\(.file), \(.api)): add \($form), then run `pr:open` again"
    end;

# The dropped comment lines past which a body states the facts it keeps
# (#6004). A rewrite of a source's comments drops tens of lines, and a fix
# that rewords one comment drops one or two.
def facts_threshold: 20;

# The refusals of `## Facts kept` (#6004) for a change that drops
# `facts_threshold` comment lines or more.
def facts_kept:
  (.comments // []) as $sources
  | ([$sources[].dropped] | add // 0) as $dropped
  | select($dropped >= facts_threshold)
  | "`| Source | Claim | Class | Where it lands |`" as $table
  | ($sources | map(select(.dropped > 0)) | sort_by(-.dropped, .path) | .[:5] | map("`\(.path)` (\(.dropped))") | join(", ")) as $most
  | (.body | section("Facts kept")) as $section
  | "the change drops \($dropped) comment lines that it does not add back, \(facts_threshold) or more (most in \($most))" as $count
  | if $section == null then
      "\($count), and the body lacks `## Facts kept`: write the table \($table) with one row for each claim the rewrite drops, or `none — <reason>`, then run `pr:open` again"
    else [$section | lead | rows | select((.cells[0] // "" | ascii_downcase) != "source")] as $rows
    | if ($rows | length) == 0 then
        if any($section[]; test("^none\\s+—\\s*\\S")) then empty
        else "\($count), and the body's `## Facts kept` holds no row and no `none — <reason>`: write the table \($table), or the reason no claim is dropped, then run `pr:open` again"
        end
      else $rows[]
      | (.cells[2] // "" | ascii_downcase) as $class
      | (.cells[3] // "") as $lands
      | if ($class | IN("needed", "noise", "borderline") | not) then
          "the `## Facts kept` row `\(.line)` has no class: write `needed`, `noise` or `borderline` in its third cell, then run `pr:open` again"
        elif $class == "needed" and ($lands | test("\\S") | not) then
          "the `## Facts kept` row `\(.line)` is `needed` and names no landing: write where its claim lands in its fourth cell, then run `pr:open` again"
        elif $class == "noise" and ($lands | test("\\S") | not) then
          "the `## Facts kept` row `\(.line)` is `noise` and gives no reason: write why the claim stays out in its fourth cell, then run `pr:open` again"
        elif $class == "borderline" and ($lands | test("#2917\\b") | not) then
          "the `## Facts kept` row `\(.line)` is `borderline` and names no finding on #2917: name it in its fourth cell, then run `pr:open` again"
        else empty
        end
      end
    end;

# A speedup claim of the body (#3479, the algorithm-first ruling of #320): a
# factor or a percentage that says the change runs faster, or a speedup that
# carries a number. The word alone, as prose about speedups writes it, claims
# none.
def speedup:
  test("\\b[0-9]+(\\.[0-9]+)?\\s*(x|×|times)\\s+(faster|quicker|the speed|speed-?ups?)\\b"; "i")
  or test("(^|[^a-z0-9])[0-9]+(\\.[0-9]+)?\\s*%\\s+(faster|quicker|speed-?ups?)\\b"; "i")
  or test("\\bspeed-?ups? of\\s+[0-9]"; "i")
  or (test("\\b(faster|quicker) than\\b"; "i") and test("[0-9]"));

# The refusals of the body's speedup claims (#3479). Each claim names the
# corpus that its number is over and the algorithmic baseline that it is
# measured against, as `corpus:` and `baseline:` on the claim's own line or
# table row. A comparison against `main` alone measures no algorithm. The
# check reads the body alone, outside its code blocks, its code spans and its
# HTML comments, so a quoted example claims nothing.
def speedups:
  .body
  | gsub("(?s)<!--.*?-->"; "")
  | lines
  | reduce .[] as $line ({fenced: false, claims: []};
      if $line | test("^\\s*(```|~~~)") then .fenced = (.fenced | not)
      elif .fenced then .
      elif $line | gsub("`[^`]*`"; "") | speedup then .claims += [$line]
      else . end)
  | .claims[]
  | ([if test("\\bcorpus:"; "i") | not then "its corpus (`corpus: <the inputs the number is over>`)" else empty end,
      if test("\\bbaseline:"; "i") | not then "its algorithmic baseline (`baseline: <the algorithm it is measured against>`)" else empty end]) as $lacks
  | select($lacks | length > 0)
  | "the body's line `\(gsub("^\\s+|\\s+$"; ""))` claims a speedup without \($lacks | join(" and ")): name both on the claim's line (#3479, the algorithm-first ruling of #320), then run `pr:open` again";

claim, sources, citations, readings, concerns, defects, surface, keywords, viewed, refactorings, collectors, engineering_answers, ceilings, api_budget, facts_kept, speedups
