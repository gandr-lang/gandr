# Whether `pr:open` opens a body: one line per refusal to print, a `note: `
# line per finding it prints and opens anyway, or nothing.
#
# Input:
#   branch    the branch being opened, `<lane>-<n>-<slug>` when it works an
#             issue
#   body      the body file's text
#   issues    the issues the body works: [{number, body}]
#   mentions  per key the body supersedes, the tree's lines naming it:
#             {key: ["<path>:<line>:<text>"]}
#   concerns  `ledger/concerns.sql` at the head and at the base:
#             {ids: [id], base: [id], sites: [{concern, crate, module}]}
#   added     the paths the change adds under `crates/*/src/`
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
# The body answers the reading axes its issues select (#2522): its
# `## Readings` table, `Family · Axis · Status`, gives each selected axis
# `answered: <exemplar or site>` or `none: <reason>`, and every row a status
# from that vocabulary or `not selected`, on one of the six axes.
#
# The body names each concern it touches (#2523): an item of its
# `## Concerns`, `` - `<id>` — <verdict> ``, names a concern of the ledger
# with `within`, `consolidated: <what merged>` or `new concern: <why none
# fits>`, the last only for a row the change adds. A module or crate the
# change adds whose name is a concern's id, or the last segment of one of its
# sites' modules, belongs to that concern; where every site of it lies in
# another crate, the body declares it `consolidated`, or a `new concern`.

include "targets";
include "sections";

def vocabulary: "`taken: <site>` (the function, test or fixture), `departed: <the recorded design, the change, why>`, `declined: <reason>` or `n/a: <reason>`";
def statuses: "`answered: <exemplar or site>`, `none: <reason>` or `not selected`";
def answered: test("^(answered|none):\\s*\\S");

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
          else ($item.text | capture("^(?<disposition>taken|departed|declined|n/a):\\s*(?<evidence>.*)$") // null) as $answer
          | if $answer == null then "the `## Sources read` item `\($line)` has no disposition: end it with \(vocabulary), then run `pr:open` again"
            elif $answer.evidence == "" then "the `## Sources read` item `\($line)` leaves its `\($answer.disposition)` blank: give its evidence, \(vocabulary), then run `pr:open` again"
            else empty
            end
          end
        end);

# The refusals of `## Readings` against the axes the issues select.
def readings:
  [(.issues // [])[] | .number as $n | .body | selected[] | {n: $n, axis: .}] as $asked
  | [(.body | section("Readings") // [] | lead) | rows | select((.cells[1] // "" | ascii_downcase) != "axis")] as $rows
  | ($asked
      | map(select(.axis as $axis | [$rows[] | select(.cells[1] == $axis and (.cells[2] // "" | answered))] | length == 0))
      | unique_by(.axis)
      | if length == 0 then empty
        else "the body's `## Readings` leaves an axis its issue selects unanswered: give its row `answered: <exemplar or site>` or `none: <reason>`, then run `pr:open` again:\n" + (map("  - `\(.axis)` (#\(.n)'s `## Readings`)") | join("\n"))
        end),
    ($rows[]
      | (.cells[1] // "") as $axis
      | (.cells[2] // "") as $status
      | if ($axis | IN(axes[]) | not) then "the `## Readings` row `\(.line)` names no axis: its second cell is one of `\(axes | join("`, `"))`, then run `pr:open` again"
        elif ($status | answered) or $status == "not selected" or ([$asked[].axis] | index($axis)) then empty
        else "the `## Readings` row `\(.line)` has a status outside \(statuses): write one, then run `pr:open` again"
        end);

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

claim, sources, readings, concerns
